/*
AppleWin : An Apple //e emulator for Windows

Copyright (C) 1994-1996, Michael O'Brien
Copyright (C) 1999-2001, Oliver Schmidt
Copyright (C) 2002-2005, Tom Charlesworth
Copyright (C) 2006-2010, Tom Charlesworth, Michael Pohoreski

AppleWin is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

AppleWin is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with AppleWin; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

/* Description: 6502/65C02 emulation
 *
 * Author: Various
 */

// TO DO:
// . All these CPP macros need to be converted to inline funcs

// TeaRex's Note about illegal opcodes:
// ------------------------------------
// . I've followed the names and descriptions given in
// . "Extra Instructions Of The 65XX Series CPU"
// . by Adam Vardy, dated Sept 27, 1996.
// . The exception is, what he calls "SKB" and "SKW" I call "NOP",
// . for consistency's sake. Several other naming conventions exist.
// . Of course, only the 6502 has illegal opcodes, the 65C02 doesn't.
// . Thus they're not emulated in Enhanced //e mode. Games relying on them
// . don't run on a real Enhanced //e either. The old mixture of 65C02
// . emulation and skipping the right number of bytes for illegal 6502
// . opcodes, while working surprisingly well in practice, was IMHO
// . ill-founded in theory and has thus been removed.


// Note about bSlowerOnPagecross:
// -------------------
// . This is used to determine if a cycle needs to be added for a page-crossing.
//
// Modes that are affected:
// . ABS,X; ABS,Y; (IND),Y
//
// The following opcodes (when indexed) add a cycle if page is crossed:
// . ADC, AND, Bxx, CMP, EOR, LDA, LDX, LDY, ORA, SBC
// . NB. Those opcode that DO NOT write to memory.
// . 65C02: JMP (ABS-INDIRECT): 65C02 fixes JMP ($xxFF) bug but needs extra cycle in that case
// . 65C02: JMP (ABS-INDIRECT,X): Probably. Currently unimplemented.
//
// The following opcodes (when indexed)	 DO NOT add a cycle if page is crossed:
// . ASL, DEC, INC, LSR, ROL, ROR, STA, STX, STY
// . NB. Those opcode that DO write to memory.
//
// What about these:
// . 65C02: STZ?, TRB?, TSB?
// . Answer: TRB & TSB don't have affected addressing modes
// .         STZ probably doesn't add a cycle since otherwise it would be slower than STA which doesn't make sense.
//
// NB. 'Zero-page indexed' opcodes wrap back to zero-page.
// .   The same goes for all the zero-page indirect modes.
//
// NB2. bSlowerOnPagecross can't be used for r/w detection, as these
// .    opcodes don't init this flag:
// . $EC CPX ABS (since there's no addressing mode of CPY which has variable cycle number)
// . $CC CPY ABS (same)
//
// 65C02 info:
// .  Read-modify-write instructions abs indexed in same page take 6 cycles (cf. 7 cycles for 6502)
// .  ASL, DEC, INC, LSR, ROL, ROR
// .  This should work now (but makes bSlowerOnPagecross even less useful for r/w detection)
//
// . Thanks to Scott Hemphill for the verified CMOS ADC and SBC algorithm! You rock.
// . And thanks to the VICE team for the NMOS ADC and SBC algorithms as well as the
// . algorithms for those illops which involve ADC or SBC. You rock too.


#include "StdAfx.h"

#include "CPU.h"
#include "Core.h"
#include "CardManager.h"
#include "Memory.h"
#include "Mockingboard.h"
#include "MouseInterface.h"
#ifdef USE_SPEECH_API
#include "Speech.h"
#endif
#include "SynchronousEventManager.h"
#include "NTSC.h"
#include "Log.h"

#include "z80emu.h"
#include "Z80VICE/z80.h"
#include "Z80VICE/z80mem.h"

#include "YamlHelper.h"

#define LOG_IRQ_TAKEN_AND_RTI 0

#define	 SHORTOPCODES  22
#define	 BENCHOPCODES  33

// What is this 6502 code? Compressed 6502 code -- see: CpuSetupBenchmark()
static BYTE benchopcode[BENCHOPCODES] = {
	0x06,0x16,0x24,0x45,0x48,0x65,0x68,0x76,
	0x84,0x85,0x86,0x91,0x94,0xA4,0xA5,0xA6,
	0xB1,0xB4,0xC0,0xC4,0xC5,0xE6,
	0x19,0x6D,0x8D,0x99,0x9D,0xAD,0xB9,0xBD,
	0xDD,0xED,0xEE
};

regsrec regs;
unsigned __int64 g_nCumulativeCycles = 0;

static ULONG g_nCyclesExecuted;	// # of cycles executed up to last IO access
//static signed long g_uInternalExecutedCycles;

//

// Assume all interrupt sources assert until the device is told to stop:
// - eg by r/w to device's register or a machine reset

static bool g_bCritSectionValid = false;	// Deleting CritialSection when not valid causes crash on Win98
static CRITICAL_SECTION g_CriticalSection;	// To guard /g_bmIRQ/ & /g_bmNMI/
static volatile UINT32 g_bmIRQ = 0;
static volatile UINT32 g_bmNMI = 0;
static volatile BOOL g_bNmiFlank = FALSE; // Positive going flank on NMI line

static bool g_irqDefer1Opcode = false;
static bool g_interruptInLastExecutionBatch = false;	// Last batch of executed cycles included an interrupt (IRQ/NMI)

//

static eCpuType g_MainCPU = CPU_65C02;
static eCpuType g_ActiveCPU = CPU_65C02;

eCpuType GetMainCpu(void)
{
	return g_MainCPU;
}

void SetMainCpu(eCpuType cpu)
{
	_ASSERT(cpu != CPU_Z80);
	if (cpu == CPU_Z80)
		return;

	g_MainCPU = cpu;
}

static bool IsCpu65C02(eApple2Type apple2Type)
{
	// NB. All Pravets clones are 6502 (GH#307)
	return (apple2Type == A2TYPE_APPLE2EENHANCED) || (apple2Type == A2TYPE_TK30002E) || (apple2Type & A2TYPE_APPLE2C); 
}

eCpuType ProbeMainCpuDefault(eApple2Type apple2Type)
{
	return IsCpu65C02(apple2Type) ? CPU_65C02 : CPU_6502;
}

void SetMainCpuDefault(eApple2Type apple2Type)
{
	SetMainCpu( ProbeMainCpuDefault(apple2Type) );
}

eCpuType GetActiveCpu(void)
{
	return g_ActiveCPU;
}

void SetActiveCpu(eCpuType cpu)
{
	g_ActiveCPU = cpu;
}

bool IsIrqAsserted(void)
{
	return g_bmIRQ ? true : false;
}

bool Is6502InterruptEnabled(void)
{
	return !(regs.ps & AF_INTERRUPT);
}

void ResetCyclesExecutedForDebugger(void)
{
	g_nCyclesExecuted = 0;
}

bool IsInterruptInLastExecution(void)
{
	return g_interruptInLastExecutionBatch;
}

//

#include "CPU/cpu_general.inl"
#include "CPU/cpu_instructions.inl"

/****************************************************************************
*
*  OPCODE TABLE
*
***/

#ifdef _DEBUG
static unsigned __int64 g_nCycleIrqStart;
static unsigned __int64 g_nCycleIrqEnd;
static UINT g_nCycleIrqTime;

static UINT g_nIdx = 0;
static const UINT BUFFER_SIZE = 4096;	// 80 secs
static UINT g_nBuffer[BUFFER_SIZE];
static UINT g_nMean = 0;
static UINT g_nMin = 0xFFFFFFFF;
static UINT g_nMax = 0;
#endif

static __forceinline void DoIrqProfiling(DWORD uCycles)
{
#ifdef _DEBUG
	if(regs.ps & AF_INTERRUPT)
		return;		// Still in Apple's ROM

#if LOG_IRQ_TAKEN_AND_RTI
	LogOutput("ISR-end\n\n");
#endif

	g_nCycleIrqEnd = g_nCumulativeCycles + uCycles;
	g_nCycleIrqTime = (UINT) (g_nCycleIrqEnd - g_nCycleIrqStart);

	if(g_nCycleIrqTime > g_nMax) g_nMax = g_nCycleIrqTime;
	if(g_nCycleIrqTime < g_nMin) g_nMin = g_nCycleIrqTime;

	if(g_nIdx == BUFFER_SIZE)
		return;

	g_nBuffer[g_nIdx] = g_nCycleIrqTime;
	g_nIdx++;

	if(g_nIdx == BUFFER_SIZE)
	{
		UINT nTotal = 0;
		for(UINT i=0; i<BUFFER_SIZE; i++)
			nTotal += g_nBuffer[i];

		g_nMean = nTotal / BUFFER_SIZE;
	}
#endif
}

//===========================================================================

#ifdef USE_SPEECH_API

const USHORT COUT1 = 0xFDF0;			// GH#934 - ProDOS: COUT1 better than using COUT/$FDED
const USHORT BASICOUT = 0xC307;			// GH#934 - 80COL: use BASICOUT

const UINT OUTPUT_BUFFER_SIZE = 256;
char g_OutputBuffer[OUTPUT_BUFFER_SIZE+1+1];	// +1 for EOL, +1 for NULL
UINT OutputBufferIdx = 0;
bool bEscMode = false;

void CaptureCOUT(void)
{
	const char ch = regs.a & 0x7f;

	if (ch == 0x07)			// Bell
	{
		// Ignore
	}
	else if (ch == 0x08)	// Backspace
	{
		if (OutputBufferIdx)
			OutputBufferIdx--;
	}
	else if (ch == 0x0A)	// LF
	{
		// Ignore
	}
	else if (ch == 0x0D)	// CR
	{
		if (bEscMode)
		{
			bEscMode = false;
		}
		else if (OutputBufferIdx)
		{
			g_OutputBuffer[OutputBufferIdx] = 0;
			g_Speech.Speak(g_OutputBuffer);

#ifdef _DEBUG
			g_OutputBuffer[OutputBufferIdx] = '\n';
			g_OutputBuffer[OutputBufferIdx+1] = 0;
			OutputDebugString(g_OutputBuffer);
#endif

			OutputBufferIdx = 0;
		}
	}
	else if (ch == 0x1B)	// Escape
	{
		bEscMode = bEscMode ? false : true;		// Toggle mode
	}
	else if (ch >= ' ' && ch <= '~')
	{
		if (OutputBufferIdx < OUTPUT_BUFFER_SIZE && !bEscMode)
			g_OutputBuffer[OutputBufferIdx++] = ch;
	}
}

#endif

//===========================================================================

//#define DBG_HDD_ENTRYPOINT
#if defined(_DEBUG) && defined(DBG_HDD_ENTRYPOINT)
// Output a debug msg whenever the HDD f/w is called or jump to.
static void DebugHddEntrypoint(const USHORT PC)
{
	static bool bOldPCAtC7xx = false;
	static WORD OldPC = 0;
	static UINT Count = 0;

	if ((PC >> 8) == 0xC7)
	{
		if (!bOldPCAtC7xx /*&& PC != 0xc70a*/)
		{
			Count++;
			LogOutput("HDD Entrypoint: $%04X\n", PC);
		}

		bOldPCAtC7xx = true;
	}
	else
	{
		bOldPCAtC7xx = false;
	}
	OldPC = PC;
}
#endif

static __forceinline void Fetch (BYTE& iOpcode, ULONG uExecutedCycles)
{
	const USHORT PC = regs.pc;

#if defined(_DEBUG) && defined(DBG_HDD_ENTRYPOINT)
	DebugHddEntrypoint(PC);
#endif

	iOpcode = ((PC & 0xF000) == 0xC000)
	    ? IORead[(PC>>4) & 0xFF](PC,PC,0,0,uExecutedCycles)	// Fetch opcode from I/O memory, but params are still from mem[]
		: *(mem+PC);

#ifdef USE_SPEECH_API
	if ((PC == COUT1 || PC == BASICOUT) && g_Speech.IsEnabled() && !g_bFullSpeed)
		CaptureCOUT();
#endif

	regs.pc++;
}

//#define ENABLE_NMI_SUPPORT	// Not used - so don't enable
static __forceinline bool NMI(ULONG& uExecutedCycles, BOOL& flagc, BOOL& flagn, BOOL& flagv, BOOL& flagz)
{
#ifdef ENABLE_NMI_SUPPORT
	if (!g_bNmiFlank)
		return false;

	// NMI signals are only serviced once
	g_bNmiFlank = FALSE;
#ifdef _DEBUG
	g_nCycleIrqStart = g_nCumulativeCycles + uExecutedCycles;
#endif
	PUSH(regs.pc >> 8)
	PUSH(regs.pc & 0xFF)
	EF_TO_AF
	PUSH(regs.ps & ~AF_BREAK)
	regs.ps = regs.ps | AF_INTERRUPT & ~AF_DECIMAL;
	regs.pc = * (WORD*) (mem+0xFFFA);
	UINT uExtraCycles = 0;	// Needed for CYC(a) macro
	CYC(7);
	g_interruptInLastExecutionBatch = true;
	return true;
#else
	return false;
#endif
}

static __forceinline void CheckSynchronousInterruptSources(UINT cycles, ULONG uExecutedCycles)
{
	g_SynchronousEventMgr.Update(cycles, uExecutedCycles);
}

// NB. No need to save to save-state, as IRQ() follows CheckSynchronousInterruptSources(), and IRQ() always sets it to false.
bool g_irqOnLastOpcodeCycle = false;

static __forceinline bool IRQ(ULONG& uExecutedCycles, BOOL& flagc, BOOL& flagn, BOOL& flagv, BOOL& flagz)
{
	bool irqTaken = false;

	if (g_bmIRQ && !(regs.ps & AF_INTERRUPT))
	{
		// if interrupt (eg. from 6522) occurs on opcode's last cycle, then defer IRQ by 1 opcode
		if (g_irqOnLastOpcodeCycle && !g_irqDefer1Opcode)
		{
			g_irqOnLastOpcodeCycle = false;
			g_irqDefer1Opcode = true;	// if INT occurs again on next opcode, then do NOT defer
			return false;
		}

		g_irqDefer1Opcode = false;

		// IRQ signals are deasserted when a specific r/w operation is done on device
#ifdef _DEBUG
		g_nCycleIrqStart = g_nCumulativeCycles + uExecutedCycles;
#endif
		PUSH(regs.pc >> 8)
		PUSH(regs.pc & 0xFF)
		EF_TO_AF
		PUSH(regs.ps & ~AF_BREAK)
		regs.ps = (regs.ps | AF_INTERRUPT) & (~AF_DECIMAL);
		regs.pc = * (WORD*) (mem+0xFFFE);
		UINT uExtraCycles = 0;	// Needed for CYC(a) macro
		CYC(7);
#if defined(_DEBUG) && LOG_IRQ_TAKEN_AND_RTI
		std::string irq6522;
		MB_Get6522IrqDescription(irq6522);
		const char* pSrc =	(g_bmIRQ & 1) ? irq6522.c_str() :
							(g_bmIRQ & 2) ? "SPEECH" :
							(g_bmIRQ & 4) ? "SSC" :
							(g_bmIRQ & 8) ? "MOUSE" : "UNKNOWN";
		LogOutput("IRQ (%08X) (%s)\n", (UINT)g_nCycleIrqStart, pSrc);
#endif
		g_interruptInLastExecutionBatch = true;
		irqTaken = true;
	}

	g_irqOnLastOpcodeCycle = false;
	return irqTaken;
}

//===========================================================================

#define READ _READ_WITH_IO_F8xx
#define WRITE(value) _WRITE_WITH_IO_F8xx(value)
#define HEATMAP_X(address)

#include "CPU/cpu6502.h"  // MOS 6502

#undef READ
#undef WRITE

//-------

#define READ _READ
#define WRITE(value) _WRITE(value)

#include "CPU/cpu65C02.h" // WDC 65C02

#undef READ
#undef WRITE
#undef HEATMAP_X

//-----------------

#define READ Heatmap_ReadByte_With_IO_F8xx(addr, uExecutedCycles)
#define WRITE(value) Heatmap_WriteByte_With_IO_F8xx(addr, value, uExecutedCycles);

#define HEATMAP_X(address) Heatmap_X(address)

#include "CPU/cpu_heatmap.inl"

#define Cpu6502 Cpu6502_debug
#include "CPU/cpu6502.h"  // MOS 6502
#undef Cpu6502

#undef READ
#undef WRITE

//-------

#define READ Heatmap_ReadByte(addr, uExecutedCycles)
#define WRITE(value) Heatmap_WriteByte(addr, value, uExecutedCycles);

#define Cpu65C02 Cpu65C02_debug
#include "CPU/cpu65C02.h" // WDC 65C02
#undef Cpu65C02


//===========================================================================
//	SAP6502 code
//	(C) 2022 Matt Regan.
//	Free for use for any purpose as defined under the original GNU license agreement.
//
//	The SAP6502 midification is distributed in the hope that it will be useful,
//	but WITHOUT ANY WARRANTY; without even the implied warranty of
//	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.See the
//	GNU General Public License for more details.
//

#define		DRIVER			0
#define		LOAD			4
#define		CONSTANT		8
#define		ALUOP			12
#define		UCOUNTERRESET	0x000020000
#define		PCCLOCKLO		0x000040000		
#define		PCCLOCKHI		0x000080000
#define		IREGLOAD		0x000100000
#define		MEMACCESS		0x000200000
#define		MWRITE			0x000400000
#define		PCSEL			0x000800000
#define		FLAGSELECT		24
#define		CARRYZERO		0x0008000000
#define		CARRYONE		0x0010000000
#define		UPDATENZ		0x0020000000
#define		UPDATEC			0x0040000000
#define		UPDATEV			0x0080000000
#define		NOBCD			0x0100000000
#define		FLAGINST		0x0200000000
#define		SHIFTRIGHT		0x0400000000
#define		SBC				0x0800000000
#define		BITOP			0x1000000000
#define		PCSELBAR		0x2000000000
#define		MREAD			0x4000000000

#define		EASEL			0x0000

#define ALU	    0
#define AREG	1
#define BREG	2
#define PCH		3
#define SPREG	4
#define EBH		5
#define PCL		6
#define AH		7
#define EBL		8
#define IREG	9
#define STREG	10
#define EAH		11
#define XREG	12
#define YREG	13
#define EAL		14
#define CONSTR	15

#define HIZ		14

#define		FLAGBIT				0x10000
#define		NFLAG			7
#define		VFLAG			6
#define		PFLAG			5
#define		UFLAG			4 
#define		DFLAG			3
#define		IFLAG			2
#define		ZFLAG			1
#define		CFLAG			0

#define		ALUAND			0x1b
#define		ALUORA			0x1e
#define		ALUXOR			0x16
#define		ALUAREG			0x1f
#define		ALUBREG			0x1a
#define		ALUADC			0x09
#define		ALUSBC			0x06

//	Main data structure for storing the microcode
#define		MICROCODESIZE	0x20000
#define		INSTRUCTIONS	0x100
unsigned long long g_controlROM[MICROCODESIZE];
int g_maxStep[INSTRUCTIONS];
bool g_SAPInitialized = false;
bool pflag = false, uflag = false;

unsigned char g_SAPRegisters[16];

unsigned long long g_EPROM[0x20000];
bool	writeEPROM = true;
void WriteEPROM()
{
	if (!writeEPROM) return;
	for (int i = 0; i < 0x20000; i++) {
		g_EPROM[i] = g_controlROM[i] ^
			(UCOUNTERRESET | PCCLOCKLO | PCCLOCKHI | MEMACCESS | MWRITE | PCSEL | UPDATEC | UPDATENZ | UPDATEV | FLAGINST | SHIFTRIGHT | SBC | BITOP);
		if ((g_controlROM[i] & PCSEL)) g_EPROM[i] |= PCSELBAR;
		if ((g_controlROM[i] & MWRITE)) g_EPROM[i] |= MREAD;
	}
	FILE* fp;
	for (int rom = 0; rom < 5; rom++) { 
		char fname[40];
		sprintf_s(fname, "D:\\AppleWinSAP\\SAP6502_ROM%d.bin", rom);
		fopen_s(&fp, fname, "w+b");
		for (int i = 0; i < 0x20000; i++) {
			fputc((g_EPROM[i] >> (rom * 8)) & 0xff, fp);
		}
		fclose(fp);
	}
	writeEPROM = false;
}

void	SetMicroInstruction(int instr, unsigned long long value)
{
	g_controlROM[(instr + ((g_maxStep[instr]) << 8))] = value;
	g_controlROM[FLAGBIT | (instr + ((g_maxStep[instr]) << 8))] = value;
	g_maxStep[instr] ++;
}

void	SetMicroInstruction(int instr, unsigned long long value, bool flag)
{
	if (!flag) g_controlROM[(instr + ((g_maxStep[instr]) << 8))] = value;
	else {
		g_controlROM[FLAGBIT | (instr + ((g_maxStep[instr]) << 8))] = value;
		g_maxStep[instr] ++;
	}
}

void ProgramRESET()
{
	for (int instruction = 0; instruction < 0x100; instruction++) {
		g_maxStep[instruction] = 24;
		SetMicroInstruction(instruction, (EAL << LOAD) | (CONSTR << DRIVER) | (0x0c << CONSTANT));						//	EAL = 0xfc
		SetMicroInstruction(instruction, (EAH << LOAD) | (CONSTR << DRIVER) | (0x0f << CONSTANT));						//	EAH = 0xff
		SetMicroInstruction(instruction, (PCL << LOAD) | (HIZ << DRIVER)	| MEMACCESS | PCCLOCKLO );  				//	Read PCL
		SetMicroInstruction(instruction, (EAL << LOAD) | (CONSTR << DRIVER) | (0x0d << CONSTANT));						//	EAL = 0xfd
		SetMicroInstruction(instruction, (PCH << LOAD) | (HIZ << DRIVER)    | MEMACCESS | PCCLOCKHI );					//	Read PCH
		SetMicroInstruction(instruction, (SPREG << LOAD) | (CONSTR << DRIVER) | (0x0f << CONSTANT) | UCOUNTERRESET);	//	Read SPREG = 0xff
	}
}


void	DecodeIMM(unsigned char instr)
{
	SetMicroInstruction(instr, (EAL << LOAD) | (PCL << DRIVER) | PCSEL);
	SetMicroInstruction(instr, (EAH << LOAD) | (PCH << DRIVER) | PCCLOCKLO | PCCLOCKHI | PCSEL);
}

void	DecodeREL(unsigned char instr)
{
	SetMicroInstruction(instr, 0);					//	Need a NOP so PCCLOCK occurs
	SetMicroInstruction(instr, (BREG << LOAD) | (HIZ << DRIVER) | PCCLOCKLO | PCCLOCKHI | PCSEL | MEMACCESS);
	SetMicroInstruction(instr, (EAL << LOAD) | (ALU << DRIVER) | (ALUBREG  << ALUOP) | (UFLAG << FLAGSELECT));
	SetMicroInstruction(instr, (EAH << LOAD) | (CONSTR << DRIVER) | (0x00 << CONSTANT), 0);
	SetMicroInstruction(instr, (EAH << LOAD) | (CONSTR << DRIVER) | (0x0f << CONSTANT), 1);

}

void	DecodeZPG(unsigned char instr)
{
	SetMicroInstruction(instr, (EAH << LOAD) | (CONSTR << DRIVER));
	SetMicroInstruction(instr, (EAL << LOAD) | (HIZ << DRIVER) | MEMACCESS | PCCLOCKLO | PCCLOCKHI | PCSEL);	
}

void	DecodeZPX(unsigned char instr)
{
	SetMicroInstruction(instr, (BREG << LOAD) | (XREG << DRIVER));											//	BREG <- XREG
	SetMicroInstruction(instr, (AH << LOAD)   | (HIZ << DRIVER) | MEMACCESS | PCCLOCKLO | PCCLOCKHI | PCSEL); //	AH <- MEM[PC++];
	SetMicroInstruction(instr, (EAL << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | CARRYZERO);	//	EAL <- AH + BREG
	SetMicroInstruction(instr, (EAH << LOAD) | (CONSTR << DRIVER));											//	EAH <- 0
}

void	DecodeZPY(unsigned char instr)
{
	SetMicroInstruction(instr, (BREG << LOAD) | (YREG << DRIVER));											//	BREG <- YREG
	SetMicroInstruction(instr, (AH << LOAD)  | (HIZ << DRIVER) | MEMACCESS | PCCLOCKLO | PCCLOCKHI | PCSEL); //	AH <- MEM[PC++];
	SetMicroInstruction(instr, (EAL << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | CARRYZERO);	//	EAL <- AH + BREG
	SetMicroInstruction(instr, (EAH << LOAD) | (CONSTR << DRIVER));											//	EAH <- 0
}


void	DecodeABS(unsigned char instr)
{
	SetMicroInstruction(instr, 0);		//	Need NOPs so PCCLOCK occurs
	SetMicroInstruction(instr, (EAL << LOAD) | (HIZ << DRIVER) | MEMACCESS | PCCLOCKLO | PCCLOCKHI | PCSEL);
	SetMicroInstruction(instr, 0);		//	Need NOPs so PCCLOCK occurs
	SetMicroInstruction(instr, (EAH << LOAD) | (HIZ << DRIVER) | MEMACCESS | PCCLOCKLO | PCCLOCKHI | PCSEL);
}

void	DecodeABX(unsigned char instr)
{
	SetMicroInstruction(instr, (BREG << LOAD) | (XREG << DRIVER));											//	BREG <- XREG
	SetMicroInstruction(instr, (AH << LOAD) | (HIZ << DRIVER) | MEMACCESS | PCCLOCKLO | PCCLOCKHI | PCSEL);	//	AH <- MEM[PC++];
	SetMicroInstruction(instr, (BREG << LOAD) | (XREG << DRIVER));											//	BREG <- XREG
	SetMicroInstruction(instr, (EAL << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | CARRYZERO |
								(PFLAG << FLAGSELECT));														//	EAL <- AH + BREG

	//	Need to use different pathway depending on PFLAG	(page boundary crossed)
	SetMicroInstruction(instr, (BREG << LOAD) | (0 << CONSTANT) | (CONSTR << DRIVER), 0);					//	BREG <- 0								//	EAH <- 0
	SetMicroInstruction(instr, (BREG << LOAD) | (1 << CONSTANT) | (CONSTR << DRIVER), 1);					//	BREG <- 1

	SetMicroInstruction(instr, (AH << LOAD) | (HIZ << DRIVER) | MEMACCESS | PCCLOCKLO | PCCLOCKHI | PCSEL);	//	AH <- MEM[PC++];
	SetMicroInstruction(instr, (EAH << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | CARRYZERO );	//	EAL <- AH + BREG
}

void	DecodeABY (unsigned char instr)
{
	SetMicroInstruction(instr, (BREG << LOAD) | (YREG << DRIVER));											//	BREG <- YREG
	SetMicroInstruction(instr, (AH << LOAD) | (HIZ << DRIVER) | MEMACCESS | PCCLOCKLO | PCCLOCKHI | PCSEL);	//	AH <- MEM[PC++];
	SetMicroInstruction(instr, (BREG << LOAD) | (YREG << DRIVER));											//	BREG <- YREG
	SetMicroInstruction(instr, (EAL << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | CARRYZERO |
								(PFLAG << FLAGSELECT));														//	EAL <- AH + BREG

//	Need to use different pathway depending on PFLAG	(page boundary crossed)
	SetMicroInstruction(instr, (BREG << LOAD) | (0 << CONSTANT) | (CONSTR << DRIVER), 0);					//	BREG <- 0								//	EAH <- 0
	SetMicroInstruction(instr, (BREG << LOAD) | (1 << CONSTANT) | (CONSTR << DRIVER), 1);					//	BREG <- 1

	SetMicroInstruction(instr, (AH << LOAD) | (HIZ << DRIVER) | MEMACCESS | PCCLOCKLO | PCCLOCKHI | PCSEL);	//	AH <- MEM[PC++];
	SetMicroInstruction(instr, (EAH << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | CARRYZERO);	//	EAL <- AH + BREG
}

void	DecodeXID(unsigned char instr)
{
	SetMicroInstruction(instr, (BREG << LOAD) | (XREG << DRIVER));											//	BREG <- XREG
	SetMicroInstruction(instr, (AH << LOAD) | (HIZ << DRIVER) | MEMACCESS | PCCLOCKLO | PCCLOCKHI | PCSEL);	//	AH <- MEM[PC++];
	SetMicroInstruction(instr, (BREG << LOAD) | (XREG << DRIVER));											//	BREG <- XREG
	SetMicroInstruction(instr, (EAL << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | CARRYZERO);	//	EAL <- AH + BREG
	SetMicroInstruction(instr, (EAH << LOAD) | (CONSTR << DRIVER));											//	EAH <- 0

	SetMicroInstruction(instr, (EBL << LOAD) | (HIZ << DRIVER) | MEMACCESS );								//	EBL <- MEM[EA];

	SetMicroInstruction(instr, (AH << LOAD)  | (PCL << DRIVER));	//	Really want EAL										//	AH<- EAL
	SetMicroInstruction(instr, (BREG << LOAD) | (1 << CONSTANT) | (CONSTR << DRIVER));						//	BREG <- 1
	SetMicroInstruction(instr, (EAL << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | CARRYZERO);	//	EAL <- AH + BREG
	SetMicroInstruction(instr, (EAH << LOAD) | (HIZ << DRIVER) | MEMACCESS);													//	EAH <- MEM[EA];
	SetMicroInstruction(instr, (EAL << LOAD) | (EBL << DRIVER));											//	EAL <- EBL
}

void	DecodeYID(unsigned char instr)
{
	SetMicroInstruction(instr, (EAH << LOAD) | (CONSTR << DRIVER));											//	EAH <- 0
	SetMicroInstruction(instr, (EAL << LOAD) | (HIZ << DRIVER) | MEMACCESS | PCCLOCKLO | PCCLOCKHI | PCSEL); //	EAL <- MEM[PC++];
	SetMicroInstruction(instr, (EAH << LOAD) | (CONSTR << DRIVER));											//	EAH <- 0
	SetMicroInstruction(instr, (EBL << LOAD) | (HIZ << DRIVER) | MEMACCESS);								//	EBL <- MEM[EA];

	SetMicroInstruction(instr, (AH << LOAD) | (PCL << DRIVER));		//	Really want EAL										//	AH<- EAL
	SetMicroInstruction(instr, (BREG << LOAD) | (1 << CONSTANT) | (CONSTR << DRIVER));						//	BREG <- 1
	SetMicroInstruction(instr, (EAL << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | CARRYZERO);	//	EAL <- AH + BREG

	SetMicroInstruction(instr, (EAH << LOAD) | (HIZ << DRIVER) | MEMACCESS);								//	EBL <- MEM[EA];

	SetMicroInstruction(instr, (AH << LOAD)   | (YREG << DRIVER));											//	AH <- XREG
	SetMicroInstruction(instr, (BREG << LOAD) | (EBL << DRIVER));											//	BREG <- EBL
/*
	SetMicroInstruction(instr, (EAL << LOAD)  | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | CARRYZERO |
								(PFLAG << FLAGSELECT));														//	EAL <- AH + BREG
	SetMicroInstruction(instr, (AH << LOAD) | (0 << CONSTANT) | (CONSTR << DRIVER), 0);													//	AH <- 1
	SetMicroInstruction(instr, (AH << LOAD) | (1 << CONSTANT) | (CONSTR << DRIVER), 1);													//	AH <- 1

	SetMicroInstruction(instr, (BREG << LOAD) | (PCH << DRIVER));				//	Really want EAH			//	BREG <- EAH
	SetMicroInstruction(instr, (EAH << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | CARRYZERO); //	EAH <- EAH + 1
*/

	SetMicroInstruction(instr, (EAL << LOAD)  | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | CARRYZERO |
								(PFLAG << FLAGSELECT));														//	EAL <- AH + BREG

	SetMicroInstruction(instr, (PFLAG << FLAGSELECT), 0);													//	
	SetMicroInstruction(instr, (BREG << LOAD) | (PCH << DRIVER) | (PFLAG << FLAGSELECT), 1);	//	Really want EAH			//	BREG <- EAH

	SetMicroInstruction(instr, (PFLAG << FLAGSELECT), 0);													//	
	SetMicroInstruction(instr, (AH << LOAD) | (1 << CONSTANT) | (CONSTR << DRIVER) | 
								(PFLAG << FLAGSELECT), 1);													//	AH <- 1

	SetMicroInstruction(instr, 0, 0);													//	
	SetMicroInstruction(instr, (EAH << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | CARRYZERO, 1); //	EAH <- EAH + 1

	
}



void	ExecuteADC (unsigned char instr)		
{
	SetMicroInstruction(instr, (BREG << LOAD) | (HIZ << DRIVER) | MEMACCESS);
	SetMicroInstruction(instr, (AH << LOAD) | (AREG << DRIVER));
	SetMicroInstruction(instr, (AREG << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | UPDATENZ | UPDATEC | UPDATEV | UCOUNTERRESET);
}

void	ExecuteALR (unsigned char instr)		{ }
void	ExecuteANC (unsigned char instr)		{ }
void	ExecuteAND (unsigned char instr)		
{
	SetMicroInstruction(instr, (BREG << LOAD) | (HIZ << DRIVER) | MEMACCESS);
	SetMicroInstruction(instr, (AH << LOAD)   | (AREG<<DRIVER));
	SetMicroInstruction(instr, (AREG << LOAD) | (ALU << DRIVER) | (ALUAND << ALUOP) | UPDATENZ | UCOUNTERRESET);
}

void	ExecuteARR (unsigned char instr)		{ }
void	ExecuteASL (unsigned char instr)		
{
	SetMicroInstruction(instr, (EBL << LOAD) | (HIZ << DRIVER) | MEMACCESS);
	SetMicroInstruction(instr, (BREG << LOAD) | (EBL << DRIVER));
	SetMicroInstruction(instr, (AH << LOAD) | (EBL << DRIVER));
	SetMicroInstruction(instr, (ALU << DRIVER) | (ALUADC << ALUOP) | CARRYZERO | UPDATENZ | UPDATEC | NOBCD | MEMACCESS | MWRITE | UCOUNTERRESET);
}

void	ExecuteASLA(unsigned char instr)		
{
	SetMicroInstruction(instr, (BREG << LOAD) | (AREG << DRIVER));
	SetMicroInstruction(instr, (AH << LOAD)   | (AREG << DRIVER));
	SetMicroInstruction(instr, (AREG << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | CARRYZERO | UPDATENZ | UPDATEC | NOBCD | UCOUNTERRESET);
}

void	ExecuteASO (unsigned char instr)		{ }
void	ExecuteAXA (unsigned char instr)		{ }
void	ExecuteAXS (unsigned char instr)		{ }

void	ExecuteBIT (unsigned char instr)
{
	SetMicroInstruction(instr, (BREG << LOAD) | (HIZ << DRIVER) | MEMACCESS);
	SetMicroInstruction(instr, (AH << LOAD) | (AREG << DRIVER));
	SetMicroInstruction(instr, (ALU << LOAD) | (ALU << DRIVER) | (ALUAND << ALUOP) | UPDATENZ | UPDATEV | BITOP | UCOUNTERRESET);
}

void	ExecuteBRA(unsigned char instr)
{
	int checkFlag;
	bool branchIf;

	switch(instr) {
	case 0x10:		checkFlag = NFLAG;		branchIf = false;		break;
	case 0x30:		checkFlag = NFLAG;		branchIf = true;		break;
	case 0x50:		checkFlag = VFLAG;		branchIf = false;		break;
	case 0x70:		checkFlag = VFLAG;		branchIf = true;		break;
	case 0x90:		checkFlag = CFLAG;		branchIf = false;		break;
	case 0xb0:		checkFlag = CFLAG;		branchIf = true;		break;
	case 0xd0:		checkFlag = ZFLAG;		branchIf = false;		break;
	case 0xf0:		checkFlag = ZFLAG;		branchIf = true;		break;
	default:		return;
	}
	SetMicroInstruction(instr, (STREG << DRIVER) | (checkFlag << FLAGSELECT));

	if (branchIf) {
		SetMicroInstruction(instr, UCOUNTERRESET, 0);
		SetMicroInstruction(instr, (AH << LOAD) | (PCL << DRIVER) | PCSEL, 1);
	}
	else {
		SetMicroInstruction(instr, (AH << LOAD) | (PCL << DRIVER) | PCSEL, 0);
		SetMicroInstruction(instr, UCOUNTERRESET, 1);
	}
	SetMicroInstruction(instr, (PCL << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | PCCLOCKLO | NOBCD | CARRYZERO | (PFLAG << FLAGSELECT));

	SetMicroInstruction(instr, (BREG << LOAD) | (PCH << DRIVER) | (PFLAG << FLAGSELECT));	//	Really want EAH

	SetMicroInstruction(instr, (AH << LOAD)   | (PCH << DRIVER) | PCSEL | (PFLAG << FLAGSELECT));
	SetMicroInstruction(instr, (PCH << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | PCCLOCKHI | NOBCD | CARRYZERO,  0);
	SetMicroInstruction(instr, (PCH << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | PCCLOCKHI | NOBCD | CARRYONE,   1);
	SetMicroInstruction(instr, UCOUNTERRESET);
}


void	ExecuteBRK (unsigned char instr)
{
	SetMicroInstruction(instr, (EAL << LOAD) | (SPREG << DRIVER));								//	EAL <- SPREG
	SetMicroInstruction(instr, (EAH << LOAD) | (CONSTR << DRIVER) | (0x01 << CONSTANT));		//	EAH <- 1

	//	MEM[EA] = PCH
	SetMicroInstruction(instr, (EBH << LOAD) | (PCH << DRIVER) | PCSEL);						//	EBH <- PCH
	SetMicroInstruction(instr, (EBH << DRIVER) | MEMACCESS | MWRITE);							//	MEM[EA] <- EBH

	//	EAL = SPREG-1
	SetMicroInstruction(instr, (BREG << LOAD) | (SPREG << DRIVER));								//	BREG <- SPREG
	SetMicroInstruction(instr, (AH << LOAD) | (CONSTR << DRIVER) | (0x0f << CONSTANT));			//	AH <- 0xff
	SetMicroInstruction(instr, (EAL << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | CARRYZERO);	//	EAL <- AH + BREG

	//	MEM [EA] = PCL
	SetMicroInstruction(instr, (EBH << LOAD) | (PCL << DRIVER) | PCSEL);						//	EBH <- PCL
	SetMicroInstruction(instr, (EBH << DRIVER) | MEMACCESS | MWRITE);							//	MEM[EA] <- EBH

	//	EAL = SPREG-2
	SetMicroInstruction(instr, (AH << LOAD) | (CONSTR << DRIVER) | (0x0e << CONSTANT));			//	AH <- 0xff
	SetMicroInstruction(instr, (EAL << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | CARRYZERO);	//	EAL <- AH + BREG
	//	MEM [EA] = STREG;
	SetMicroInstruction(instr, (STREG << DRIVER) | MEMACCESS | MWRITE);							//	MEM[EA] <- EBH

	//	SPREG-=3;
	SetMicroInstruction(instr, (AH << LOAD) | (CONSTR << DRIVER) | (0x0d << CONSTANT));			//	AH <- 0xff
	SetMicroInstruction(instr, (SPREG << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | CARRYZERO);	//	SPREG <- AH + BREG

	SetMicroInstruction(instr, (EAL << LOAD) | (CONSTR << DRIVER) | (0x0e << CONSTANT));						//	EAL = 0xfe
	SetMicroInstruction(instr, (EAH << LOAD) | (CONSTR << DRIVER) | (0x0f << CONSTANT));						//	EAH = 0xff
	SetMicroInstruction(instr, (PCL << LOAD) | (HIZ << DRIVER) | MEMACCESS | PCCLOCKLO);  						//	Read PCL
	SetMicroInstruction(instr, (EAL << LOAD) | (CONSTR << DRIVER) | (0x0f << CONSTANT));						//	EAL = 0xff
	SetMicroInstruction(instr, (PCH << LOAD) | (HIZ << DRIVER) | MEMACCESS | PCCLOCKHI);						//	Read PCH
	SetMicroInstruction(instr, (HIZ << DRIVER) | UCOUNTERRESET);		
}


void	ExecuteCMP (unsigned char instr)		
{
	SetMicroInstruction(instr, (BREG << LOAD) | (HIZ << DRIVER) | MEMACCESS);
	SetMicroInstruction(instr, (AH << LOAD) | (AREG << DRIVER));
	SetMicroInstruction(instr, (EBL << LOAD) | (ALU << DRIVER) | (ALUSBC << ALUOP) | NOBCD | CARRYONE | UPDATENZ | UPDATEC | UCOUNTERRESET);
}

void	ExecuteCPX (unsigned char instr)		
{
	SetMicroInstruction(instr, (BREG << LOAD) | (HIZ << DRIVER) | MEMACCESS);
	SetMicroInstruction(instr, (AH << LOAD) | (XREG << DRIVER));
	SetMicroInstruction(instr, (EBL << LOAD) | (ALU << DRIVER) | (ALUSBC << ALUOP) | NOBCD | CARRYONE | UPDATENZ | UPDATEC | UCOUNTERRESET);
}


void	ExecuteCPY (unsigned char instr)		
{
	SetMicroInstruction(instr, (BREG << LOAD) | (HIZ << DRIVER) | MEMACCESS);
	SetMicroInstruction(instr, (AH << LOAD) | (YREG << DRIVER));
	SetMicroInstruction(instr, (EBL << LOAD) | (ALU << DRIVER) | (ALUSBC << ALUOP) | NOBCD | CARRYONE | UPDATENZ | UPDATEC | UCOUNTERRESET);
}


void	ExecuteDCM (unsigned char instr)		{ }

void	ExecuteDEC (unsigned char instr)
{
	SetMicroInstruction(instr, (BREG << LOAD)  | (HIZ << DRIVER) | MEMACCESS);
	SetMicroInstruction(instr, (AH << LOAD)    | (CONSTR << DRIVER) | (0x0f << CONSTANT));
	SetMicroInstruction(instr, (ALU << DRIVER) | (ALUADC << ALUOP) | CARRYZERO | UPDATENZ | NOBCD | MEMACCESS | MWRITE | UCOUNTERRESET);
}

void	ExecuteDEX (unsigned char instr)		
{
	SetMicroInstruction(instr, (BREG << LOAD) | (XREG << DRIVER));
	SetMicroInstruction(instr, (AH << LOAD)   | (CONSTR << DRIVER) | (0x0f << CONSTANT));
	SetMicroInstruction(instr, (XREG << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | CARRYZERO | UPDATENZ | NOBCD | UCOUNTERRESET);
}

void	ExecuteDEY (unsigned char instr)
{
	SetMicroInstruction(instr, (BREG << LOAD) | (YREG << DRIVER));
	SetMicroInstruction(instr, (AH << LOAD) | (CONSTR << DRIVER) | (0x0f << CONSTANT));
	SetMicroInstruction(instr, (YREG << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | CARRYZERO | UPDATENZ | NOBCD | UCOUNTERRESET);
}

void	ExecuteEOR (unsigned char instr)
{
	SetMicroInstruction(instr, (BREG << LOAD) | (HIZ << DRIVER) | MEMACCESS);
	SetMicroInstruction(instr, (AH << LOAD)   | (AREG << DRIVER));
	SetMicroInstruction(instr, (AREG << LOAD) | (ALU << DRIVER) | (ALUXOR << ALUOP) | UPDATENZ | UCOUNTERRESET);
}

void	ExecuteFOP(unsigned char instr) {
	SetMicroInstruction(instr, FLAGINST | UCOUNTERRESET);
}


void	ExecuteHLT (unsigned char instr)		{ }

void	ExecuteINS (unsigned char instr)		{ }

void	ExecuteINC (unsigned char instr)		
{
	SetMicroInstruction(instr, (BREG << LOAD) | (HIZ << DRIVER) | MEMACCESS);
	SetMicroInstruction(instr, (AH << LOAD) | (CONSTR << DRIVER) | (0x01 << CONSTANT));
	SetMicroInstruction(instr, (ALU << DRIVER) | (ALUADC << ALUOP) | CARRYZERO | UPDATENZ | NOBCD | MEMACCESS | MWRITE | UCOUNTERRESET);
}

void	ExecuteINX (unsigned char instr)		
{
	SetMicroInstruction(instr, (BREG << LOAD) | (XREG << DRIVER));
	SetMicroInstruction(instr, (AH << LOAD) | (CONSTR << DRIVER) | (0x01 << CONSTANT));
	SetMicroInstruction(instr, (XREG << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | CARRYZERO | UPDATENZ | NOBCD | UCOUNTERRESET);
}

void	ExecuteINY (unsigned char instr)		
{
	SetMicroInstruction(instr, (BREG << LOAD) | (YREG << DRIVER));
	SetMicroInstruction(instr, (AH << LOAD) | (CONSTR << DRIVER) | (0x01 << CONSTANT));
	SetMicroInstruction(instr, (YREG << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | CARRYZERO | UPDATENZ | NOBCD | UCOUNTERRESET);
}

void	ExecuteJMP (unsigned char instr)		
{
	SetMicroInstruction(instr, 0);
	SetMicroInstruction(instr, (EBL << LOAD) | (HIZ << DRIVER) | MEMACCESS | PCCLOCKLO | PCCLOCKHI | PCSEL);
	SetMicroInstruction(instr, 0);
	SetMicroInstruction(instr, (PCH << LOAD) | (HIZ << DRIVER) | PCCLOCKHI | MEMACCESS | PCSEL );
	SetMicroInstruction(instr, (PCL << LOAD) | PCCLOCKLO | (EBL << DRIVER) );
	SetMicroInstruction(instr, UCOUNTERRESET);
}

void	ExecuteJMPI(unsigned char instr)		
{
	SetMicroInstruction(instr, 0);
	SetMicroInstruction(instr, (EBL << LOAD) | (HIZ << DRIVER) | MEMACCESS | PCCLOCKLO | PCCLOCKHI | PCSEL);
	SetMicroInstruction(instr, 0);
	SetMicroInstruction(instr, (PCH << LOAD) | (HIZ << DRIVER) | PCCLOCKHI | MEMACCESS | PCSEL);
	SetMicroInstruction(instr, (PCL << LOAD) | PCCLOCKLO | (EBL << DRIVER) );
	SetMicroInstruction(instr, 0);

	SetMicroInstruction(instr, (EBL << LOAD) | (HIZ << DRIVER) | MEMACCESS | PCCLOCKLO | PCCLOCKHI | PCSEL);
	SetMicroInstruction(instr, 0);
	SetMicroInstruction(instr, (PCH << LOAD) | (HIZ << DRIVER)	|PCCLOCKHI | MEMACCESS | PCSEL);
	SetMicroInstruction(instr, (PCL << LOAD) | PCCLOCKLO | (EBL << DRIVER) );
	SetMicroInstruction(instr, UCOUNTERRESET);
}

void	ExecuteJSR (unsigned char instr)		
{
	//	EBL = MEM[PC++]
	SetMicroInstruction(instr, (EAL << LOAD) | (SPREG << DRIVER));								//	EAL <- SPREG
	SetMicroInstruction(instr, (EBL << LOAD) | (HIZ << DRIVER) | MEMACCESS | PCCLOCKLO | PCCLOCKHI | PCSEL);

	//	EA = 0x0100 | SPREG
	SetMicroInstruction(instr, (EAH << LOAD) | (CONSTR << DRIVER) | (0x01 << CONSTANT));		//	EAH <- 1

	//	MEM[EA] = PCH
	SetMicroInstruction(instr, (EBH << LOAD) | (PCH << DRIVER)  | PCSEL);						//	EBH <- PCH
	SetMicroInstruction(instr, (EBH << DRIVER) | MEMACCESS | MWRITE);							//	MEM[EA] <- EBH

	//	EAL = --SPREG
	SetMicroInstruction(instr, (BREG << LOAD) | (SPREG << DRIVER));								//	BREG <- SPREG
	SetMicroInstruction(instr, (AH << LOAD) | (CONSTR << DRIVER) | (0x0f << CONSTANT));			//	AH <- 0xff
	SetMicroInstruction(instr, (EAL << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | CARRYZERO );	//	EAL <- AH + BREG

	//	MEM [EA] = PCL
	SetMicroInstruction(instr, (EBH << LOAD) | (PCL << DRIVER) | PCSEL);						//	EBH <- PCL
	SetMicroInstruction(instr, (EBH << DRIVER) | MEMACCESS | MWRITE);							//	MEM[EA] <- EBH

	//	SPREG--;
	SetMicroInstruction(instr, (BREG << LOAD) | (PCL << DRIVER));								//	BREG <- EAL
	SetMicroInstruction(instr, (SPREG << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | CARRYZERO);	//	SPREG <- AH + BREG
	
	//	PCH = MEM[PC]
	SetMicroInstruction(instr, (PCH << LOAD) | (HIZ << DRIVER) | MEMACCESS | PCCLOCKHI | PCSEL);								//	PCL -< MEM[PC] 

	//	PCL = EBL
	SetMicroInstruction(instr, (PCL << LOAD) | PCCLOCKLO | (EBL << DRIVER) );				//	PCL <- EBL

	SetMicroInstruction(instr, UCOUNTERRESET);								//	PCL -< MEM[PC] 

}

void	ExecuteLAS (unsigned char instr)		{ }

void	ExecuteLDA (unsigned char instr)		
{ 
	SetMicroInstruction(instr, (BREG << LOAD) | (HIZ << DRIVER) | MEMACCESS);
	SetMicroInstruction(instr, (AREG << LOAD) | (ALU << DRIVER) | (ALUBREG << ALUOP) | UPDATENZ | UCOUNTERRESET );
}

void	ExecuteLDX(unsigned char instr)
{
	SetMicroInstruction(instr, (BREG << LOAD) | (HIZ << DRIVER) | MEMACCESS);
	SetMicroInstruction(instr, (XREG << LOAD) | (ALU << DRIVER) | (ALUBREG << ALUOP) | UPDATENZ | UCOUNTERRESET);
}

void	ExecuteLDY(unsigned char instr)
{
	SetMicroInstruction(instr, (BREG << LOAD) | (HIZ << DRIVER) | MEMACCESS);
	SetMicroInstruction(instr, (YREG << LOAD) | (ALU << DRIVER) | (ALUBREG << ALUOP) | UPDATENZ | UCOUNTERRESET);
}

void	ExecuteLAX (unsigned char instr)		{ }
void	ExecuteLAY (unsigned char instr)		{ }
void	ExecuteLSE (unsigned char instr)		{ }

void	ExecuteLSR (unsigned char instr)		
{
	SetMicroInstruction(instr, (BREG << LOAD) | (HIZ << DRIVER) | MEMACCESS);
	SetMicroInstruction(instr, (ALU << DRIVER) | (ALUBREG << ALUOP) | UPDATENZ | UPDATEC | CARRYZERO | MEMACCESS | MWRITE | UCOUNTERRESET | SHIFTRIGHT);
}

void	ExecuteLSRA(unsigned char instr) 
{
	SetMicroInstruction(instr, (BREG << LOAD) | (AREG << DRIVER));
	SetMicroInstruction(instr, (AREG << LOAD) | (ALU << DRIVER) | (ALUBREG << ALUOP) | UPDATENZ | UPDATEC | CARRYZERO | UCOUNTERRESET | SHIFTRIGHT);
}

void	ExecuteNOP (unsigned char instr)		
{
	SetMicroInstruction(instr, UCOUNTERRESET | PCSEL );
}

void	ExecuteOAL (unsigned char instr)		{ }
void	ExecuteORA (unsigned char instr)		
{
	SetMicroInstruction(instr, (BREG << LOAD) | (HIZ << DRIVER) | MEMACCESS);
	SetMicroInstruction(instr, (AH << LOAD) | (AREG << DRIVER));
	SetMicroInstruction(instr, (AREG << LOAD) | (ALU << DRIVER) | (ALUORA << ALUOP) | UPDATENZ | UCOUNTERRESET);
}


void	ExecutePHA (unsigned char instr)		
{
	SetMicroInstruction(instr, (EAL << LOAD) | (SPREG << DRIVER));								//	EAL <- SPREG
	SetMicroInstruction(instr, (EAH << LOAD) | (CONSTR << DRIVER) | (0x01 << CONSTANT) );		//	EAH <- 1
	SetMicroInstruction(instr, (AREG << DRIVER) | MEMACCESS | MWRITE );							//	MEM[EA] <- AREG

	SetMicroInstruction(instr, (BREG << LOAD) | (SPREG << DRIVER));								//	BREG <- SPREG
	SetMicroInstruction(instr, (AH << LOAD)   | (CONSTR << DRIVER) | (0x0f << CONSTANT));		//	AH <- 0xff
	SetMicroInstruction(instr, (SPREG << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | CARRYZERO | UCOUNTERRESET);	//	SPREG <- AH + BREG
}

void	ExecutePHP (unsigned char instr)		
{
	SetMicroInstruction(instr, (EAL << LOAD) | (SPREG << DRIVER));								//	EAL <- SPREG
	SetMicroInstruction(instr, (EAH << LOAD) | (CONSTR << DRIVER) | (0x01 << CONSTANT));		//	EAH <- 1
	SetMicroInstruction(instr, (STREG << DRIVER) | MEMACCESS | MWRITE);							//	MEM[EA] <- STREG

	SetMicroInstruction(instr, (BREG << LOAD) | (SPREG << DRIVER));								//	BREG <- SPREG
	SetMicroInstruction(instr, (AH << LOAD) | (CONSTR << DRIVER) | (0x0f << CONSTANT));		//	AH <- 0xff
	SetMicroInstruction(instr, (SPREG << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | CARRYZERO | UCOUNTERRESET);	//	SPREG <- AH + BREG
}

void	ExecutePLA (unsigned char instr)		
{ 
	SetMicroInstruction(instr, (BREG << LOAD) | (SPREG << DRIVER));								//	BREG <- SPREG
	SetMicroInstruction(instr, (AH << LOAD) | (CONSTR << DRIVER) | (0x01 << CONSTANT));			//	AH <- 0x01
	SetMicroInstruction(instr, (SPREG << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | CARRYZERO );	//	SPREG <- AH + BREG

	SetMicroInstruction(instr, (EAL << LOAD) | (SPREG << DRIVER));								//	EAL <- SPREG
	SetMicroInstruction(instr, (EAH << LOAD) | (CONSTR << DRIVER) | (0x01 << CONSTANT));		//	EAH <- 1
	SetMicroInstruction(instr, (BREG << LOAD) | (HIZ << DRIVER) | MEMACCESS );					//	BREG <- MEM[EA] 
	SetMicroInstruction(instr, (AREG << LOAD) | (ALU << DRIVER) | (ALUBREG << ALUOP) | UPDATENZ | UCOUNTERRESET);	//	AREG <- BREG
}

void	ExecutePLP (unsigned char instr)		
{
	SetMicroInstruction(instr, (BREG << LOAD) | (SPREG << DRIVER));								//	BREG <- SPREG
	SetMicroInstruction(instr, (AH << LOAD) | (CONSTR << DRIVER) | (0x01 << CONSTANT));			//	AH <- 0x01
	SetMicroInstruction(instr, (SPREG << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | CARRYZERO);	//	SPREG <- AH + BREG

	SetMicroInstruction(instr, (EAL << LOAD) | (SPREG << DRIVER));								//	EAL <- SPREG
	SetMicroInstruction(instr, (EAH << LOAD) | (CONSTR << DRIVER) | (0x01 << CONSTANT));		//	EAH <- 1
	SetMicroInstruction(instr, (BREG << LOAD) | (HIZ << DRIVER) | MEMACCESS);					//	BREG <- MEM[EA] 
	SetMicroInstruction(instr, (STREG << LOAD) | (ALU << DRIVER) | (ALUBREG << ALUOP) | UPDATENZ | UCOUNTERRESET);	//	STREG <- BREG
}

void	ExecuteRLA (unsigned char instr)		{ }

void	ExecuteROL(unsigned char instr)
{
	SetMicroInstruction(instr, (EBL << LOAD)  | (HIZ << DRIVER) | MEMACCESS);
	SetMicroInstruction(instr, (BREG << LOAD) | (EBL << DRIVER));
	SetMicroInstruction(instr, (AH << LOAD)   | (EBL << DRIVER));
	SetMicroInstruction(instr,				    (ALU << DRIVER) | (ALUADC << ALUOP) | UPDATENZ | UPDATEC | NOBCD | MEMACCESS | MWRITE | UCOUNTERRESET);
}

void	ExecuteROLA(unsigned char instr)
{
	SetMicroInstruction(instr, (BREG << LOAD) | (AREG << DRIVER));
	SetMicroInstruction(instr, (AH << LOAD)   | (AREG << DRIVER));
	SetMicroInstruction(instr, (AREG << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | UPDATENZ | UPDATEC | NOBCD | UCOUNTERRESET);
}

void	ExecuteROR(unsigned char instr)
{
	SetMicroInstruction(instr, (BREG << LOAD) | (HIZ << DRIVER) | MEMACCESS);
	SetMicroInstruction(instr, (ALU << DRIVER) | (ALUBREG << ALUOP) | UPDATENZ | UPDATEC | MEMACCESS | MWRITE | UCOUNTERRESET | SHIFTRIGHT);
}

void	ExecuteRORA(unsigned char instr)		
{
	SetMicroInstruction(instr, (BREG << LOAD) | (AREG << DRIVER));
	SetMicroInstruction(instr, (AREG << LOAD) | (ALU << DRIVER) | (ALUBREG << ALUOP) | UPDATENZ | UPDATEC | UCOUNTERRESET | SHIFTRIGHT);
}

void	ExecuteRRA (unsigned char instr)		{ }
void	ExecuteRTI (unsigned char instr)
{
	//	EA = 0x100 | (SPREG+1)
	SetMicroInstruction(instr, (BREG << LOAD) | (SPREG << DRIVER));								//	BREG <- SPREG
	SetMicroInstruction(instr, (AH << LOAD) | (CONSTR << DRIVER) | (0x01 << CONSTANT));			//	AH <- 0x01
	SetMicroInstruction(instr, (EAL << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | CARRYZERO);	//	EAL <- AH + BREG
	SetMicroInstruction(instr, (EAH << LOAD) | (CONSTR << DRIVER) | (0x01 << CONSTANT));		//	EAH <- 1

	//	STREG = MEM[EA]
	SetMicroInstruction(instr, (STREG << LOAD) | (HIZ << DRIVER) | MEMACCESS);												//	STREG <- MEM[EA]

	//	EAL = SPREG + 2
	SetMicroInstruction(instr, (AH << LOAD) | (CONSTR << DRIVER) | (0x02 << CONSTANT));											//	AH <- 0x02
	SetMicroInstruction(instr, (EAL << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | CARRYZERO);						//	EAL <- AH + BREG

	//	PCL = MEM[EA]
	SetMicroInstruction(instr, (PCL << LOAD) | PCCLOCKLO | (HIZ << DRIVER) | MEMACCESS);										//	PCL <- MEM[EA]

	//	EAL = SPREG + 3
	SetMicroInstruction(instr, (AH << LOAD) | (CONSTR << DRIVER) | (0x03 << CONSTANT));										//	AH <- 0x03
	SetMicroInstruction(instr, (EAL << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | CARRYZERO);						//	EAL <- AH + BREG

	//	PCH = MEM[EA]
	SetMicroInstruction(instr, (PCH << LOAD) | PCCLOCKHI | (HIZ << DRIVER) | MEMACCESS);										//	PCH <- MEM[EA]

	//	SPREG = SPREG + 3;
	//	
	SetMicroInstruction(instr, (SPREG << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | CARRYZERO | UCOUNTERRESET);						//	EAL <- AH + BREG
}

void	ExecuteRTS(unsigned char instr)
{
	//	EA = 0x100 | (++SPREG)
	SetMicroInstruction(instr, (BREG << LOAD) | (SPREG << DRIVER));								//	BREG <- SPREG
	SetMicroInstruction(instr, (AH << LOAD) | (CONSTR << DRIVER) | (0x01 << CONSTANT));			//	AH <- 0x01
	SetMicroInstruction(instr, (EAL << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | CARRYZERO);	//	EAL <- AH + BREG
	SetMicroInstruction(instr, (EAH << LOAD) | (CONSTR << DRIVER) | (0x01 << CONSTANT));		//	EAH <- 1

	//	PCL = MEM[EA]
	SetMicroInstruction(instr, (PCL << LOAD) | PCCLOCKLO | (HIZ << DRIVER) | MEMACCESS );										//	PCL <- MEM[EA]

	//	EAL++
	SetMicroInstruction(instr, (BREG << LOAD) | (PCL << DRIVER));	//	Really want EAL								//	BREG <- EAL
	SetMicroInstruction(instr, (EAL << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | CARRYZERO);	//	EAL <- AH + BREG

	//	PCH = MEM[EA]
	SetMicroInstruction(instr, (PCH << LOAD) | PCCLOCKHI | (HIZ << DRIVER) | MEMACCESS);										//	PCH <- MEM[EA]
	SetMicroInstruction(instr, 0);
	//	SPREG = EAL
	//	PC++
	SetMicroInstruction(instr, (SPREG << LOAD) | (PCL << DRIVER) | PCCLOCKLO | PCCLOCKHI );	//	Really want EAL							//	SPREG <- EAL
	SetMicroInstruction(instr, UCOUNTERRESET);
}

void	ExecuteSAX (unsigned char instr)		{ }
void	ExecuteSAY (unsigned char instr)		{ }
void	ExecuteSBC (unsigned char instr)		
{
	SetMicroInstruction(instr, (BREG << LOAD) | (HIZ << DRIVER) | MEMACCESS);
	SetMicroInstruction(instr, (AH << LOAD) | (AREG << DRIVER));
	SetMicroInstruction(instr, (AREG << LOAD) | (ALU << DRIVER) | (ALUSBC << ALUOP) | UPDATENZ | UPDATEC | UPDATEV | UCOUNTERRESET);
}

void	ExecuteSTA(unsigned char instr) { SetMicroInstruction(instr, (AREG << DRIVER) | MEMACCESS | MWRITE | UCOUNTERRESET); }
void	ExecuteSTX(unsigned char instr) { SetMicroInstruction(instr, (XREG << DRIVER) | MEMACCESS | MWRITE | UCOUNTERRESET); }
void	ExecuteSTY(unsigned char instr) { SetMicroInstruction(instr, (YREG << DRIVER) | MEMACCESS | MWRITE | UCOUNTERRESET); }

void	ExecuteTAS (unsigned char instr)		{ }
void	ExecuteTAX (unsigned char instr)
{
	SetMicroInstruction(instr, (BREG << LOAD) | (AREG << DRIVER));
	SetMicroInstruction(instr, (XREG << LOAD) | (ALU << DRIVER) | (ALUBREG << ALUOP) | UPDATENZ | UCOUNTERRESET);
}

void	ExecuteTAY (unsigned char instr)		
{
	SetMicroInstruction(instr, (BREG << LOAD) | (AREG << DRIVER));
	SetMicroInstruction(instr, (YREG << LOAD) | (ALU << DRIVER) | (ALUBREG << ALUOP) | UPDATENZ | UCOUNTERRESET);
}

void	ExecuteTSX (unsigned char instr)		
{
	SetMicroInstruction(instr, (BREG << LOAD) | (SPREG << DRIVER));
	SetMicroInstruction(instr, (XREG << LOAD) | (ALU << DRIVER) | (ALUBREG << ALUOP) | UPDATENZ | UCOUNTERRESET);
}

void	ExecuteTXA (unsigned char instr)		
{
	SetMicroInstruction(instr, (BREG << LOAD) | (XREG << DRIVER));
	SetMicroInstruction(instr, (AREG << LOAD) | (ALU << DRIVER) | (ALUBREG << ALUOP) | UPDATENZ | UCOUNTERRESET);
}

void	ExecuteTXS(unsigned char instr)
{
	SetMicroInstruction(instr, (SPREG << LOAD) | (XREG << DRIVER) | UCOUNTERRESET);
}

void	ExecuteTYA (unsigned char instr)		
{
	SetMicroInstruction(instr, (BREG << LOAD) | (YREG << DRIVER));
	SetMicroInstruction(instr, (AREG << LOAD) | (ALU << DRIVER) | (ALUBREG << ALUOP) | UPDATENZ | UCOUNTERRESET);
}


void	ExecuteXAA (unsigned char instr)		{ }
void	ExecuteXAS (unsigned char instr)		{ }

void	Executeror (unsigned char instr)		{ }


bool	ProgramControlROM()
{
	if (!g_SAPInitialized) g_SAPInitialized = true;
	else return false;

	for (int i = 0; i < MICROCODESIZE; i++) g_controlROM[i] = 0x00;
	
	//	Program step zero for all instructions
	for (int instr = 0; instr < INSTRUCTIONS; instr++) {
		SetMicroInstruction(instr, IREGLOAD | PCCLOCKLO | PCCLOCKHI | (HIZ << DRIVER) | MEMACCESS | PCSEL);
	}

	for (int instr = 0; instr < INSTRUCTIONS; instr++) {
		switch (instr) {
								
		case 0x00:							ExecuteBRK (instr);	  break;
		case 0x01:	DecodeXID (instr);		ExecuteORA (instr);	  break;
		case 0x02:							ExecuteHLT (instr);	  break;	// invalid
		case 0x03:	DecodeXID (instr);		ExecuteASO (instr);	  break;	// invalid
		case 0x04:	DecodeZPG (instr);		ExecuteNOP (instr);	  break;	// invalid
		case 0x05:	DecodeZPG (instr);		ExecuteORA (instr);	  break;
		case 0x06:	DecodeZPG (instr);		ExecuteASL (instr);	  break;
		case 0x07:	DecodeZPG (instr);		ExecuteASO (instr);	  break;	// invalid
		case 0x08:							ExecutePHP (instr);	  break;
		case 0x09:	DecodeIMM (instr);		ExecuteORA (instr);	  break;
		case 0x0A:							ExecuteASLA(instr);	  break;
		case 0x0B:	DecodeIMM (instr);		ExecuteANC (instr);	  break;	// invalid
		case 0x0C:	DecodeABS (instr);		ExecuteNOP (instr);	  break;	// invalid
		case 0x0D:	DecodeABS (instr);		ExecuteORA (instr);	  break;
		case 0x0E:	DecodeABS (instr);		ExecuteASL (instr);	  break;
		case 0x0F:	DecodeABS (instr);		ExecuteASO (instr);	  break;	// invalid
		case 0x10:	DecodeREL (instr);		ExecuteBRA (instr);	  break;
		case 0x11:	DecodeYID (instr);		ExecuteORA (instr);	  break;
		case 0x12:							ExecuteHLT (instr);	  break;	// invalid
		case 0x13:	DecodeYID (instr);		ExecuteASO (instr);	  break;	// invalid
		case 0x14:	DecodeZPX (instr);		ExecuteNOP (instr);	  break;	// invalid
		case 0x15:	DecodeZPX (instr);		ExecuteORA (instr);	  break;
		case 0x16:	DecodeZPX (instr);		ExecuteASL (instr);	  break;
		case 0x17:	DecodeZPX (instr);		ExecuteASO (instr);	  break;	// invalid
		case 0x18:							ExecuteFOP (instr);	  break;
		case 0x19:	DecodeABY (instr);		ExecuteORA (instr);	  break;
		case 0x1A:							ExecuteNOP (instr);	  break;	// invalid
		case 0x1B:	DecodeABY (instr);		ExecuteASO (instr);	  break;	// invalid
		case 0x1C:	DecodeABX (instr);		ExecuteNOP (instr);	  break;	// invalid
		case 0x1D:	DecodeABX (instr);		ExecuteORA (instr);	  break;
		case 0x1E:	DecodeABX (instr);		ExecuteASL (instr);	  break;
		case 0x1F:	DecodeABX (instr);		ExecuteASO (instr);	  break;	// invalid
		case 0x20:							ExecuteJSR (instr);	  break;
		case 0x21:	DecodeXID (instr);		ExecuteAND (instr);	  break;
		case 0x22:							ExecuteHLT (instr);	  break;	// invalid
		case 0x23:	DecodeXID (instr);		ExecuteRLA (instr);	  break;	// invalid
		case 0x24:	DecodeZPG (instr);		ExecuteBIT (instr);	  break;
		case 0x25:	DecodeZPG (instr);		ExecuteAND (instr);	  break;
		case 0x26:	DecodeZPG (instr);		ExecuteROL (instr);	  break;
		case 0x27:	DecodeZPG (instr);		ExecuteRLA (instr);	  break;	// invalid
		case 0x28:							ExecutePLP (instr);	  break;
		case 0x29:	DecodeIMM (instr);		ExecuteAND (instr);	  break;
		case 0x2A:							ExecuteROLA(instr);	  break;
		case 0x2B:	DecodeIMM (instr);		ExecuteANC (instr);	  break;	// invalid
		case 0x2C:	DecodeABS (instr);		ExecuteBIT (instr);	  break;
		case 0x2D:	DecodeABS (instr);		ExecuteAND (instr);	  break;
		case 0x2E:	DecodeABS (instr);		ExecuteROL (instr);	  break;
		case 0x2F:	DecodeABS (instr);		ExecuteRLA (instr);	  break;	// invalid
		case 0x30:	DecodeREL (instr);		ExecuteBRA (instr);	  break;
		case 0x31:	DecodeYID (instr);		ExecuteAND (instr);	  break;
		case 0x32:							ExecuteHLT (instr);	  break;	// invalid
		case 0x33:	DecodeYID (instr);		ExecuteRLA (instr);	  break;	// invalid
		case 0x34:	DecodeZPX (instr);		ExecuteNOP (instr);	  break;	// invalid
		case 0x35:	DecodeZPX (instr);		ExecuteAND (instr);	  break;
		case 0x36:	DecodeZPX (instr);		ExecuteROL (instr);	  break;
		case 0x37:	DecodeZPX (instr);		ExecuteRLA (instr);	  break;	// invalid
		case 0x38:							ExecuteFOP (instr);	  break;
		case 0x39:	DecodeABY (instr);		ExecuteAND (instr);	  break;
		case 0x3A:							ExecuteNOP (instr);	  break;	// invalid
		case 0x3B:	DecodeABY (instr);		ExecuteRLA (instr);	  break;	// invalid
		case 0x3C:	DecodeABX (instr);		ExecuteNOP (instr);	  break;	// invalid
		case 0x3D:	DecodeABX (instr);		ExecuteAND (instr);	  break;
		case 0x3E:	DecodeABX (instr);		ExecuteROL (instr);	  break;
		case 0x3F:	DecodeABX (instr);		ExecuteRLA (instr);	  break;	// invalid
		case 0x40:							ExecuteRTI (instr);	  break;
		case 0x41:	DecodeXID (instr);		ExecuteEOR (instr);	  break;
		case 0x42:							ExecuteHLT (instr);	  break;	// invalid
		case 0x43:	DecodeXID (instr);		ExecuteLSE (instr);	  break;	// invalid
		case 0x44:	DecodeZPG (instr);		ExecuteNOP (instr);	  break;	// invalid
		case 0x45:	DecodeZPG (instr);		ExecuteEOR (instr);	  break;
		case 0x46:	DecodeZPG (instr);		ExecuteLSR (instr);	  break;
		case 0x47:	DecodeZPG (instr);		ExecuteLSE (instr);	  break;	// invalid
		case 0x48:							ExecutePHA (instr);	  break;
		case 0x49:	DecodeIMM (instr);		ExecuteEOR (instr);	  break;
		case 0x4A:							ExecuteLSRA(instr);	  break;
		case 0x4B:	DecodeIMM (instr);		ExecuteALR (instr);	  break;	// invalid
		case 0x4C:							ExecuteJMP (instr);	  break;
		case 0x4D:	DecodeABS (instr);		ExecuteEOR (instr);	  break;
		case 0x4E:	DecodeABS (instr);		ExecuteLSR (instr);	  break;
		case 0x4F:	DecodeABS (instr);		ExecuteLSE (instr);	  break;	// invalid
		case 0x50:	DecodeREL (instr);		ExecuteBRA (instr);	  break;
		case 0x51:	DecodeYID (instr);		ExecuteEOR (instr);	  break;
		case 0x52:							ExecuteHLT (instr);	  break;	// invalid
		case 0x53:	DecodeYID (instr);		ExecuteLSE (instr);	  break;	// invalid
		case 0x54:	DecodeZPX (instr);		ExecuteNOP (instr);	  break;	// invalid
		case 0x55:	DecodeZPX (instr);		ExecuteEOR (instr);	  break;
		case 0x56:	DecodeZPX (instr);		ExecuteLSR (instr);	  break;
		case 0x57:	DecodeZPX (instr);		ExecuteLSE (instr);	  break;	// invalid
		case 0x58:							ExecuteFOP (instr);	  break;
		case 0x59:	DecodeABY (instr);		ExecuteEOR (instr);	  break;
		case 0x5A:							ExecuteNOP (instr);	  break;	// invalid
		case 0x5B:	DecodeABY (instr);		ExecuteLSE (instr);	  break;	// invalid
		case 0x5C:	DecodeABX (instr);		ExecuteNOP (instr);	  break;	// invalid
		case 0x5D:	DecodeABX (instr);		ExecuteEOR (instr);	  break;
		case 0x5E:	DecodeABX (instr);		ExecuteLSR (instr);	  break;
		case 0x5F:	DecodeABX (instr);		ExecuteLSE (instr);	  break;	// invalid
		case 0x60:							ExecuteRTS (instr);	  break;
		case 0x61:	DecodeXID (instr);		ExecuteADC (instr);	  break;
		case 0x62:							ExecuteHLT (instr);	  break;	// invalid
		case 0x63:	DecodeXID (instr);		ExecuteRRA (instr);	  break;	// invalid
		case 0x64:	DecodeZPG (instr);		ExecuteNOP (instr);	  break;	// invalid
		case 0x65:	DecodeZPG (instr);		ExecuteADC (instr);	  break;
		case 0x66:	DecodeZPG (instr);		ExecuteROR (instr);	  break;
		case 0x67:	DecodeZPG (instr);		ExecuteRRA (instr);	  break;	// invalid
		case 0x68:							ExecutePLA (instr);	  break;
		case 0x69:	DecodeIMM (instr);		ExecuteADC (instr);	  break;
		case 0x6A:							ExecuteRORA(instr);	  break;
		case 0x6B:	DecodeIMM (instr);		ExecuteARR (instr);	  break;	// invalid
		case 0x6C:							ExecuteJMPI(instr);	  break; // GH#264
		case 0x6D:	DecodeABS (instr);		ExecuteADC (instr);	  break;
		case 0x6E:	DecodeABS (instr);		ExecuteROR (instr);	  break;
		case 0x6F:	DecodeABS (instr);		ExecuteRRA (instr);	  break;	// invalid
		case 0x70:	DecodeREL (instr);		ExecuteBRA (instr);	  break;
		case 0x71:	DecodeYID (instr);		ExecuteADC (instr);	  break;
		case 0x72:							ExecuteHLT (instr);	  break;	// invalid
		case 0x73:	DecodeYID (instr);		ExecuteRRA (instr);	  break;	// invalid
		case 0x74:	DecodeZPX (instr);		ExecuteNOP (instr);	  break;	// invalid
		case 0x75:	DecodeZPX (instr);		ExecuteADC (instr);	  break;
		case 0x76:	DecodeZPX (instr);		ExecuteROR (instr);	  break;
		case 0x77:	DecodeZPX (instr);		ExecuteRRA (instr);	  break;	// invalid
		case 0x78:							ExecuteFOP (instr);	  break;
		case 0x79:	DecodeABY (instr);		ExecuteADC (instr);	  break;
		case 0x7A:							ExecuteNOP (instr);	  break;	// invalid
		case 0x7B:	DecodeABY (instr);		ExecuteRRA (instr);	  break;	// invalid
		case 0x7C:	DecodeABX (instr);		ExecuteNOP (instr);	  break;	// invalid
		case 0x7D:	DecodeABX (instr);		ExecuteADC (instr);	  break;
		case 0x7E:	DecodeABX (instr);		ExecuteROR (instr);	  break;
		case 0x7F:	DecodeABX (instr);		ExecuteRRA (instr);	  break;	// invalid
		case 0x80:	DecodeIMM (instr);		ExecuteNOP (instr);	  break;	// invalid
		case 0x81:	DecodeXID (instr);		ExecuteSTA (instr);	  break;
		case 0x82:	DecodeIMM (instr);		ExecuteNOP (instr);	  break;	// invalid
		case 0x83:	DecodeXID (instr);		ExecuteAXS (instr);	  break;	// invalid
		case 0x84:	DecodeZPG (instr);		ExecuteSTY (instr);	  break;
		case 0x85:	DecodeZPG (instr);		ExecuteSTA (instr);	  break;
		case 0x86:	DecodeZPG (instr);		ExecuteSTX (instr);	  break;
		case 0x87:	DecodeZPG (instr);		ExecuteAXS (instr);	  break;	// invalid
		case 0x88:							ExecuteDEY (instr);	  break;
		case 0x89:	DecodeIMM (instr);		ExecuteNOP (instr);	  break;	// invalid
		case 0x8A:							ExecuteTXA (instr);	  break;
		case 0x8B:	DecodeIMM (instr);		ExecuteXAA (instr);	  break;	// invalid
		case 0x8C:	DecodeABS (instr);		ExecuteSTY (instr);	  break;
		case 0x8D:	DecodeABS (instr);		ExecuteSTA (instr);	  break;
		case 0x8E:	DecodeABS (instr);		ExecuteSTX (instr);	  break;
		case 0x8F:	DecodeABS (instr);		ExecuteAXS (instr);	  break;	// invalid
		case 0x90:	DecodeREL (instr);		ExecuteBRA (instr);	  break;
		case 0x91:	DecodeYID (instr);		ExecuteSTA (instr);	  break;
		case 0x92:							ExecuteHLT (instr);	  break;	// invalid
		case 0x93:	DecodeYID (instr);		ExecuteAXA (instr);	  break;	// invalid
		case 0x94:	DecodeZPX (instr);		ExecuteSTY (instr);	  break;
		case 0x95:	DecodeZPX (instr);		ExecuteSTA (instr);	  break;
		case 0x96:	DecodeZPY (instr);		ExecuteSTX (instr);	  break;
		case 0x97:	DecodeZPY (instr);		ExecuteAXS (instr);	  break;	// invalid
		case 0x98:							ExecuteTYA (instr);	  break;
		case 0x99:	DecodeABY (instr);		ExecuteSTA (instr);	  break;
		case 0x9A:							ExecuteTXS (instr);	  break;
		case 0x9B:	DecodeABY (instr);		ExecuteTAS (instr);	  break;	// invalid
		case 0x9C:	DecodeABX (instr);		ExecuteSAY (instr);	  break;	// invalid
		case 0x9D:	DecodeABX (instr);		ExecuteSTA (instr);	  break;
		case 0x9E:	DecodeABY (instr);		ExecuteXAS (instr);	  break;	// invalid
		case 0x9F:	DecodeABY (instr);		ExecuteAXA (instr);	  break;	// invalid
		case 0xA0:	DecodeIMM (instr);		ExecuteLDY (instr);	  break;
		case 0xA1:	DecodeXID (instr);		ExecuteLDA (instr);	  break;
		case 0xA2:	DecodeIMM (instr);		ExecuteLDX (instr);	  break;
		case 0xA3:	DecodeXID (instr);		ExecuteLAX (instr);	  break;	// invalid
		case 0xA4:	DecodeZPG (instr);		ExecuteLDY (instr);	  break;
		case 0xA5:	DecodeZPG (instr);		ExecuteLDA (instr);	  break;
		case 0xA6:	DecodeZPG (instr);		ExecuteLDX (instr);	  break;
		case 0xA7:	DecodeZPG (instr);		ExecuteLAX (instr);	  break;	// invalid
		case 0xA8:							ExecuteTAY (instr);	  break;
		case 0xA9:	DecodeIMM (instr);		ExecuteLDA (instr);	  break;
		case 0xAA:							ExecuteTAX (instr);	  break;
		case 0xAB:	DecodeIMM (instr);		ExecuteOAL (instr);	  break;	// invalid
		case 0xAC:	DecodeABS (instr);		ExecuteLDY (instr);	  break;
		case 0xAD:	DecodeABS (instr);		ExecuteLDA (instr);	  break;
		case 0xAE:	DecodeABS (instr);		ExecuteLDX (instr);	  break;
		case 0xAF:	DecodeABS (instr);		ExecuteLAX (instr);	  break;	// invalid
		case 0xB0:	DecodeREL (instr);		ExecuteBRA (instr);	  break;
		case 0xB1:	DecodeYID (instr);		ExecuteLDA (instr);	  break;
		case 0xB2:							ExecuteHLT (instr);	  break;	// invalid
		case 0xB3:	DecodeYID (instr);		ExecuteLAX (instr);	  break;	// invalid
		case 0xB4:	DecodeZPX (instr);		ExecuteLDY (instr);	  break;
		case 0xB5:	DecodeZPX (instr);		ExecuteLDA (instr);	  break;
		case 0xB6:	DecodeZPY (instr);		ExecuteLDX (instr);	  break;
		case 0xB7:	DecodeZPY (instr);		ExecuteLAX (instr);	  break;	// invalid
		case 0xB8:							ExecuteFOP (instr);	  break;
		case 0xB9:	DecodeABY (instr);		ExecuteLDA (instr);	  break;
		case 0xBA:							ExecuteTSX (instr);	  break;
		case 0xBB:	DecodeABY (instr);		ExecuteLAS (instr);	  break;	// invalid
		case 0xBC:	DecodeABX (instr);		ExecuteLDY (instr);	  break;
		case 0xBD:	DecodeABX (instr);		ExecuteLDA (instr);	  break;
		case 0xBE:	DecodeABY (instr);		ExecuteLDX (instr);	  break;
		case 0xBF:	DecodeABY (instr);		ExecuteLAX (instr);	  break;	// invalid
		case 0xC0:	DecodeIMM (instr);		ExecuteCPY (instr);	  break;
		case 0xC1:	DecodeXID (instr);		ExecuteCMP (instr);	  break;
		case 0xC2:	DecodeIMM (instr);		ExecuteNOP (instr);	  break;	// invalid
		case 0xC3:	DecodeXID (instr);		ExecuteDCM (instr);	  break;	// invalid
		case 0xC4:	DecodeZPG (instr);		ExecuteCPY (instr);	  break;
		case 0xC5:	DecodeZPG (instr);		ExecuteCMP (instr);	  break;
		case 0xC6:	DecodeZPG (instr);		ExecuteDEC (instr);	  break;
		case 0xC7:	DecodeZPG (instr);		ExecuteDCM (instr);	  break;	// invalid
		case 0xC8:							ExecuteINY (instr);	  break;
		case 0xC9:	DecodeIMM (instr);		ExecuteCMP (instr);	  break;
		case 0xCA:							ExecuteDEX (instr);	  break;
		case 0xCB:	DecodeIMM (instr);		ExecuteSAX (instr);	  break;	// invalid
		case 0xCC:	DecodeABS (instr);		ExecuteCPY (instr);	  break;
		case 0xCD:	DecodeABS (instr);		ExecuteCMP (instr);	  break;
		case 0xCE:	DecodeABS (instr);		ExecuteDEC (instr);	  break;
		case 0xCF:	DecodeABS (instr);		ExecuteDCM (instr);	  break;	// invalid
		case 0xD0:	DecodeREL (instr);		ExecuteBRA (instr);	  break;
		case 0xD1:	DecodeYID (instr);		ExecuteCMP (instr);	  break;
		case 0xD2:							ExecuteHLT (instr);	  break;	// invalid
		case 0xD3:	DecodeYID (instr);		ExecuteDCM (instr);	  break;	// invalid
		case 0xD4:	DecodeZPX (instr);		ExecuteNOP (instr);	  break;	// invalid
		case 0xD5:	DecodeZPX (instr);		ExecuteCMP (instr);	  break;
		case 0xD6:	DecodeZPX (instr);		ExecuteDEC (instr);	  break;
		case 0xD7:	DecodeZPX (instr);		ExecuteDCM (instr);	  break;	// invalid
		case 0xD8:							ExecuteFOP (instr);	  break;
		case 0xD9:	DecodeABY (instr);		ExecuteCMP (instr);	  break;
		case 0xDA:							ExecuteNOP (instr);	  break;	// invalid
		case 0xDB:	DecodeABY (instr);		ExecuteDCM (instr);	  break;	// invalid
		case 0xDC:	DecodeABX (instr);		ExecuteNOP (instr);	  break;	// invalid
		case 0xDD:	DecodeABX (instr);		ExecuteCMP (instr);	  break;
		case 0xDE:	DecodeABX (instr);		ExecuteDEC (instr);	  break;
		case 0xDF:	DecodeABX (instr);		ExecuteDCM (instr);	  break;	// invalid
		case 0xE0:	DecodeIMM (instr);		ExecuteCPX (instr);	  break;
		case 0xE1:	DecodeXID (instr);		ExecuteSBC (instr);	  break;
		case 0xE2:	DecodeIMM (instr);		ExecuteNOP (instr);	  break;	// invalid
		case 0xE3:	DecodeXID (instr);		ExecuteINS (instr);	  break;	// invalid
		case 0xE4:	DecodeZPG (instr);		ExecuteCPX (instr);	  break;
		case 0xE5:	DecodeZPG (instr);		ExecuteSBC (instr);	  break;
		case 0xE6:	DecodeZPG (instr);		ExecuteINC (instr);	  break;
		case 0xE7:	DecodeZPG (instr);		ExecuteINS (instr);	  break;	// invalid
		case 0xE8:							ExecuteINX (instr);	  break;
		case 0xE9:	DecodeIMM (instr);		ExecuteSBC (instr);	  break;
		case 0xEA:							ExecuteNOP (instr);	  break;
		case 0xEB:	DecodeIMM (instr);		ExecuteSBC (instr);	  break;	// invalid
		case 0xEC:	DecodeABS (instr);		ExecuteCPX (instr);	  break;
		case 0xED:	DecodeABS (instr);		ExecuteSBC (instr);	  break;
		case 0xEE:	DecodeABS (instr);		ExecuteINC (instr);	  break;
		case 0xEF:	DecodeABS (instr);		ExecuteINS (instr);	  break;	// invalid
		case 0xF0:	DecodeREL (instr);		ExecuteBRA (instr);	  break;
		case 0xF1:	DecodeYID (instr);		ExecuteSBC (instr);	  break;
		case 0xF2:							ExecuteHLT (instr);	  break;	// invalid
		case 0xF3:	DecodeYID (instr);		ExecuteINS (instr);	  break;	// invalid
		case 0xF4:	DecodeZPX (instr);		ExecuteNOP (instr);	  break;	// invalid
		case 0xF5:	DecodeZPX (instr);		ExecuteSBC (instr);	  break;
		case 0xF6:	DecodeZPX (instr);		ExecuteINC (instr);	  break;
		case 0xF7:	DecodeZPX (instr);		ExecuteINS (instr);	  break;	// invalid
		case 0xF8:							ExecuteFOP (instr);	  break;
		case 0xF9:	DecodeABY (instr);		ExecuteSBC (instr);	  break;
		case 0xFA:							ExecuteNOP (instr);	  break;	// invalid
		case 0xFB:	DecodeABY (instr);		ExecuteINS (instr);	  break;	// invalid
		case 0xFC:	DecodeABX (instr);		ExecuteNOP (instr);	  break;	// invalid
		case 0xFD:	DecodeABX (instr);		ExecuteSBC (instr);	  break;
		case 0xFE:	DecodeABX (instr);		ExecuteINC (instr);	  break;
		case 0xFF:	DecodeABX (instr);		ExecuteINS (instr);	  break;	// invalid
					 
		}
	}
	ProgramRESET();
	WriteEPROM();
	return true;
}

unsigned char g_updateNZ[256] = {
	0x02,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,
	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,
	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,
	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,
	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,
	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,
	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,
	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,	0x00,
	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,
	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,
	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,
	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,
	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,
	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,
	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,
	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80,	0x80
};

unsigned char ReadRegister(unsigned long long controlWire)
{
	unsigned int sum, result = 0;
	unsigned int tl = 0, t2 = 0;

	int reg = (controlWire >> DRIVER) & 0x0f;
	if (reg == 0) {
		unsigned int carryIn = (controlWire & CARRYZERO) ? 0 : g_SAPRegisters[STREG] & 0x01;
		if (controlWire & CARRYONE) carryIn = 1;

		//	ALU operation
		switch ((controlWire >> ALUOP) & 0x1f) {
		case ALUADC:
			if ((g_SAPRegisters[STREG] & (1 << DFLAG)) && (!(controlWire & NOBCD))) {
				sum = (g_SAPRegisters[AH]&0x0f) + (g_SAPRegisters[BREG]&0x0f) + carryIn;
				if (sum > 9)	sum += 6;
				sum = sum + (g_SAPRegisters[AH] & 0xf0) + (g_SAPRegisters[BREG] & 0xf0);
				if (controlWire & UPDATENZ) g_SAPRegisters[STREG] = (g_SAPRegisters[STREG] & 0x7d) | g_updateNZ[sum&0xff];
				if ((sum & 0x1f0) > 0x90) sum += 0x60;
			}
			else {
				sum = g_SAPRegisters[AH] + g_SAPRegisters[BREG] + carryIn;
				pflag = (sum & 0x100) ? true : false;
				if (controlWire & UPDATENZ) g_SAPRegisters[STREG] = (g_SAPRegisters[STREG] & 0x7d) | g_updateNZ[sum&0xff];
			}
			result = sum & 0x0ff;
			if (controlWire & UPDATEC) g_SAPRegisters[STREG] = (g_SAPRegisters[STREG] & 0xfe) + ((sum & 0x100) ? 1 : 0);
			if (controlWire & UPDATEV) {
				g_SAPRegisters[STREG] = (g_SAPRegisters[STREG] & 0xbf) |
					((((g_SAPRegisters[AH] & 0x80) == (g_SAPRegisters[BREG] & 0x80)) &&
					((g_SAPRegisters[AH] & 0x80) != (result & 0x80))) ? 0x40 : 0x00);
			}
			break;
		case ALUSBC:
			g_SAPRegisters[BREG] = g_SAPRegisters[BREG] ^ 0xff;
			if ((g_SAPRegisters[STREG] & (1 << DFLAG)) && (!(controlWire & NOBCD))) {
				sum = (g_SAPRegisters[AH]&0x0f) + (g_SAPRegisters[BREG]&0x0f) + carryIn;
				if (sum & 0x10) {
					sum = ((sum - 6) & 0x0f) | ((g_SAPRegisters[AH] & 0xf0) + (g_SAPRegisters[BREG] & 0xf0) - 0x10);
				}
				else {
					sum = sum | ((g_SAPRegisters[AH] & 0xf0) + (g_SAPRegisters[BREG] & 0xf0));
				}
				if (sum & 0x100) {
					sum -= 0x60;
				}

			}
			else {
				sum = g_SAPRegisters[AH] + g_SAPRegisters[BREG] + carryIn;
				pflag = (sum & 0x100) ? true : false;
			}
			result = sum & 0x0ff;
			if (controlWire & UPDATEV) {
				g_SAPRegisters[STREG] = (g_SAPRegisters[STREG] & 0xbf) |
					((((g_SAPRegisters[AH] & 0x80) == (g_SAPRegisters[BREG] & 0x80)) &&
					((g_SAPRegisters[AH] & 0x80) != (result & 0x80))) ? 0x40 : 0x00);
			}
			if (controlWire & UPDATENZ) g_SAPRegisters[STREG] = (g_SAPRegisters[STREG] & 0x7d) | g_updateNZ[result];
			if (controlWire & UPDATEC) g_SAPRegisters[STREG] = (g_SAPRegisters[STREG] & 0xfe) + ((sum & 0x100) ? 1 : 0);
			break;
		case ALUAND:
			result = g_SAPRegisters[AH] & g_SAPRegisters[BREG];
			if (controlWire & UPDATENZ) g_SAPRegisters[STREG] = (g_SAPRegisters[STREG] & 0x7d) | g_updateNZ[result];
			if (BITOP) {
				g_SAPRegisters[STREG] = (g_SAPRegisters[STREG] & 0x3f) | (g_SAPRegisters[BREG] & 0xc0);
			}
			break;
		case ALUORA:
			result = g_SAPRegisters[AH] | g_SAPRegisters[BREG];
			if (controlWire & UPDATENZ) g_SAPRegisters[STREG] = (g_SAPRegisters[STREG] & 0x7d) | g_updateNZ[result];
			break;
		case ALUXOR:
			result = g_SAPRegisters[AH] ^ g_SAPRegisters[BREG];
			if (controlWire & UPDATENZ) g_SAPRegisters[STREG] = (g_SAPRegisters[STREG] & 0x7d) | g_updateNZ[result];
			break;

		case ALUBREG:
			result = g_SAPRegisters[BREG];
			if (controlWire & SHIFTRIGHT) {
				g_SAPRegisters[STREG] = (g_SAPRegisters[STREG] & 0xfe) | ((result & 0x01) ? 0x01 : 0x00);
				result = (result >> 1) | (carryIn ? 0x80 : 0x00);
			}
			if (controlWire & UPDATENZ) g_SAPRegisters[STREG] = (g_SAPRegisters[STREG] & 0x7d) | g_updateNZ[result];
			break;
		default:	return 0;
		}
	}
	else { 
		if ((reg == EAL) || (reg == PCL)) {
			if (controlWire & PCSEL) reg = PCL;
			else reg = EAL;
		}
		if ((reg == EAH) || (reg == PCH)) {
			if (controlWire & PCSEL) reg = PCH;
			else reg = EAH;
		}

		return g_SAPRegisters[reg];
	}
	return result & 0xff;
}

void	WriteRegister(int reg, unsigned char wbus)
{
	g_SAPRegisters[reg & 0x0f] = wbus;
}
int icnt = 0;
void	EmulateSAP6502(ULONG uExecutedCycles)
{
	unsigned char step = 0; 
	unsigned char wbus = 0x0;
	unsigned long long controlWires = g_controlROM[0];
	icnt++;
	g_SAPRegisters[AREG] = regs.a;
	g_SAPRegisters[XREG] = regs.x;
	g_SAPRegisters[YREG] = regs.y;
	g_SAPRegisters[PCL] = (regs.pc & 0xff);
	g_SAPRegisters[PCH] = ((regs.pc>>8) & 0xff);
	g_SAPRegisters[STREG] = regs.ps;
	g_SAPRegisters[SPREG] = (regs.sp&0xff); 

	do {
		unsigned int addr = 0x00;
		if (controlWires & PCSEL) addr = g_SAPRegisters[PCL] | (g_SAPRegisters[PCH] << 8);
		else addr = g_SAPRegisters[EAL] | (g_SAPRegisters[EAH] << 8);
		if ((controlWires & MEMACCESS) && (!(controlWires & MWRITE))) {
			wbus = READ;
		}
		else wbus = ReadRegister(controlWires);
		if (controlWires & IREGLOAD) g_SAPRegisters[IREG] = wbus;

		if (controlWires & FLAGINST) {
			switch (g_SAPRegisters[IREG]) {
			case 0x18:	g_SAPRegisters[STREG] &= 0xfe;	break;	//	CLC
			case 0x38:	g_SAPRegisters[STREG] |= 0x01;	break;	//	SEC
			case 0x58:	g_SAPRegisters[STREG] &= 0xfb;	break;	//	CLI
			case 0x78:	g_SAPRegisters[STREG] |= 0x04;	break;	//	SEI
			case 0xb8:	g_SAPRegisters[STREG] &= 0xbf;	break;	//	CLV
			case 0xd8:	g_SAPRegisters[STREG] &= 0xf7;	break;	//	CLD
			case 0xf8:	g_SAPRegisters[STREG] |= 0x08;	break;	//	SED
			}
		}

		if ((controlWires & MEMACCESS) && ((controlWires & MWRITE))) {
			WRITE(wbus);
		}
		else WriteRegister((controlWires >> LOAD) & 0x0f, wbus);

		if ((controlWires & PCCLOCKLO) && (controlWires & PCCLOCKHI)) {
			if (g_SAPRegisters[PCL]++ == 0xFF) {
				g_SAPRegisters[PCH]++;
			}
		}
		step = (step + 1) & 0x1f;
		if (controlWires & UCOUNTERRESET) step = 0;
		unsigned int controlAddress = g_SAPRegisters[IREG] | (step << 8);
		if (((controlWires >> FLAGSELECT) & 0x06) == 0x4) {
			if (((controlWires >> FLAGSELECT) & 0x07) == PFLAG) controlAddress |= (pflag ? FLAGBIT : 0);
			if (((controlWires >> FLAGSELECT) & 0x07) == UFLAG) controlAddress |= ((g_SAPRegisters[BREG]&0x80) ? FLAGBIT : 0);
		}
		else {
			controlAddress |= (g_SAPRegisters[STREG] & (1 << ((controlWires >> FLAGSELECT) & 0x07))) ? FLAGBIT : 0;
		}
		controlWires = g_controlROM[controlAddress];
		g_SAPRegisters[CONSTR] = (controlWires >> CONSTANT) & 0x0f;
		if(g_SAPRegisters[CONSTR] & 0x08) g_SAPRegisters[CONSTR] |= 0xf0;	//	sign extent constant register
	} while (step != 0);
	//	Turn off decimal mode
	g_SAPRegisters[STREG] &= 0xf7;

	regs.a  = g_SAPRegisters[AREG];
	regs.x  = g_SAPRegisters[XREG];
	regs.y  = g_SAPRegisters[YREG];
	regs.pc = g_SAPRegisters[PCL] | (g_SAPRegisters[PCH] << 8);
	regs.ps = g_SAPRegisters[STREG];
	regs.sp = g_SAPRegisters[SPREG] | 0x100;
}

int		SAP6502Cycles()
{
	unsigned char instruction;
	instruction = *(mem + regs.pc);

	switch (instruction) {
//	case 0x00: return 7;
	case 0x01: return 6;
//	case 0x02: return 2;	// invalid
//	case 0x03: return 8;	// invalid
//	case 0x04: return 3;	// invalid
	case 0x05: return 3;
	case 0x06: return 5;
//	case 0x07: return 5;	// invalid
	case 0x08: return 3;
	case 0x09: return 2;
	case 0x0A: return 2;
//	case 0x0B: return 2;	// invalid
//	case 0x0C: return 4;	// invalid
	case 0x0D: return 4;
	case 0x0E: return 6;
//	case 0x0F: return 6;	// invalid
	case 0x10: return 2;
	case 0x11: return 5;
//	case 0x12: return 2;	// invalid
//	case 0x13: return 8;	// invalid
//	case 0x14: return 4;	// invalid
	case 0x15: return 4;
	case 0x16: return 6;
//	case 0x17: return 6;	// invalid
	case 0x18: return 2;
	case 0x19: return 4;
	case 0x1A: return 2;	// invalid
//	case 0x1B: return 7;	// invalid
//	case 0x1C: return 4;	// invalid
	case 0x1D: return 4;
	case 0x1E: return 7;
//	case 0x1F: return 7;	// invalid
	case 0x20: return 6;
	case 0x21: return 6;
//	case 0x22: return 2;	// invalid
//	case 0x23: return 8;	// invalid
	case 0x24: return 3;
	case 0x25: return 3;
	case 0x26: return 5;
//	case 0x27: return 5;	// invalid
	case 0x28: return 4;
	case 0x29: return 2;
	case 0x2A: return 2;
//	case 0x2B: return 2;	// invalid
	case 0x2C: return 4;
	case 0x2D: return 4;
	case 0x2E: return 6;
//	case 0x2F: return 6;	// invalid
	case 0x30: return 2;
	case 0x31: return 5;
//	case 0x32: return 2;	// invalid
//	case 0x33: return 8;	// invalid
//	case 0x34: return 4;	// invalid
	case 0x35: return 4;
	case 0x36: return 6;
//	case 0x37: return 6;	// invalid
	case 0x38: return 2;
	case 0x39: return 4;
//	case 0x3A: return 2;	// invalid
//	case 0x3B: return 7;	// invalid
//	case 0x3C: return 4;	// invalid
	case 0x3D: return 4;
	case 0x3E: return 7;
//	case 0x3F: return 7;	// invalid
	case 0x40: return 6; 
	case 0x41: return 6;
//	case 0x42: return 2;	// invalid
//	case 0x43: return 8;	// invalid
//	case 0x44: return 3;	// invalid
	case 0x45: return 3;
	case 0x46: return 5;
//	case 0x47: return 5;	// invalid
	case 0x48: return 3;
	case 0x49: return 2;
	case 0x4A: return 2;
//	case 0x4B: return 2;	// invalid
	case 0x4C: return 3;
	case 0x4D: return 4;
	case 0x4E: return 6;
//	case 0x4F: return 6;	// invalid
	case 0x50: return 2;
	case 0x51: return 5;
//	case 0x52: return 2;	// invalid
//	case 0x53: return 8;	// invalid
//	case 0x54: return 4;	// invalid
	case 0x55: return 4;
	case 0x56: return 6;
//	case 0x57: return 6;	// invalid
	case 0x58: return 2;
	case 0x59: return 4;
//	case 0x5A: return 2;	// invalid
//	case 0x5B: return 7;	// invalid
//	case 0x5C: return 4;	// invalid
	case 0x5D: return 4;
	case 0x5E: return 7;
//	case 0x5F: return 7;	// invalid
	case 0x60: return 6;
	case 0x61: return 6;
//	case 0x62: return 2;	// invalid
//	case 0x63: return 8;	// invalid
//	case 0x64: return 3;	// invalid
	case 0x65: return 3;
	case 0x66: return 5;
//	case 0x67: return 5;	// invalid
	case 0x68: return 4;
	case 0x69: return 2;
	case 0x6A: return 2;
//	case 0x6B: return 2;	// invalid
	case 0x6C: return 5; 
	case 0x6D: return 4;
	case 0x6E: return 6;
//	case 0x6F: return 6;	// invalid
	case 0x70: return 2;
	case 0x71: return 5;
//	case 0x72: return 2;	// invalid
//	case 0x73: return 8;	// invalid
//	case 0x74: return 4;	// invalid
	case 0x75: return 4;
	case 0x76: return 6;
//	case 0x77: return 6;	// invalid
	case 0x78: return 2;
	case 0x79: return 4;
//	case 0x7A: return 2;	// invalid
//	case 0x7B: return 7;	// invalid
//	case 0x7C: return 4;	// invalid
	case 0x7D: return 4;
	case 0x7E: return 7;
//	case 0x7F: return 7;	// invalid
//	case 0x80: return 2;	// invalid
	case 0x81: return 6;
//	case 0x82: return 2;	// invalid
//	case 0x83: return 6;	// invalid
	case 0x84: return 3;
	case 0x85: return 3;
	case 0x86: return 3;
//	case 0x87: return 3;	// invalid
	case 0x88: return 2;
//	case 0x89: return 2;	// invalid
	case 0x8A: return 2;
//	case 0x8B: return 2;	// invalid
	case 0x8C: return 4;
	case 0x8D: return 4;
	case 0x8E: return 4;
//	case 0x8F: return 4;	// invalid
	case 0x90: return 2;
	case 0x91: return 6;
//	case 0x92: return 2;	// invalid
//	case 0x93: return 6;	// invalid
	case 0x94: return 4;
	case 0x95: return 4;
	case 0x96: return 4;
//	case 0x97: return 4;	// invalid
	case 0x98: return 2;
	case 0x99: return 5;
	case 0x9A: return 2;
//	case 0x9B: return 5;	// invalid
//	case 0x9C: return 5;	// invalid
	case 0x9D: return 5;
//	case 0x9E: return 5;	// invalid
//	case 0x9F: return 5;	// invalid
	case 0xA0: return 2;
	case 0xA1: return 6;
	case 0xA2: return 2;
//	case 0xA3: return 6;	// invalid
	case 0xA4: return 3;
	case 0xA5: return 3;
	case 0xA6: return 3;
//	case 0xA7: return 3;	// invalid
	case 0xA8: return 2;
	case 0xA9: return 2;
	case 0xAA: return 2;
//	case 0xAB: return 2;	// invalid
	case 0xAC: return 4;
	case 0xAD: return 4;
	case 0xAE: return 4;
//	case 0xAF: return 4;	// invalid
	case 0xB0: return 2;
	case 0xB1: return 5;
//	case 0xB2: return 2;	// invalid
//	case 0xB3: return 5;	// invalid
	case 0xB4: return 4;
	case 0xB5: return 4;
	case 0xB6: return 4;
//	case 0xB7: return 4;	// invalid
	case 0xB8: return 2;
	case 0xB9: return 4;
	case 0xBA: return 2;
//	case 0xBB: return 4;	// invalid
	case 0xBC: return 4;
	case 0xBD: return 4;
	case 0xBE: return 4;
//	case 0xBF: return 4;	// invalid
	case 0xC0: return 2;
	case 0xC1: return 6;
//	case 0xC2: return 2;	// invalid
//	case 0xC3: return 8;	// invalid
	case 0xC4: return 3;
	case 0xC5: return 3;
	case 0xC6: return 5;
//	case 0xC7: return 5;	// invalid
	case 0xC8: return 2;
	case 0xC9: return 2;
	case 0xCA: return 2;
//	case 0xCB: return 2;	// invalid
	case 0xCC: return 4;
	case 0xCD: return 4;
	case 0xCE: return 6;
//	case 0xCF: return 6;	// invalid
	case 0xD0: return 2;
	case 0xD1: return 5;
//	case 0xD2: return 2;	// invalid
//	case 0xD3: return 8;	// invalid
//	case 0xD4: return 4;	// invalid
	case 0xD5: return 4;
	case 0xD6: return 6;
//	case 0xD7: return 6;	// invalid
	case 0xD8: return 2;
	case 0xD9: return 4;
//	case 0xDA: return 2;	// invalid
//	case 0xDB: return 7;	// invalid
//	case 0xDC: return 4;	// invalid
	case 0xDD: return 4;
	case 0xDE: return 7;
//	case 0xDF: return 7;	// invalid
	case 0xE0: return 2;
	case 0xE1: return 6;
//	case 0xE2: return 2;	// invalid
//	case 0xE3: return 8;	// invalid
	case 0xE4: return 3;
	case 0xE5: return 3;
	case 0xE6: return 5;
//	case 0xE7: return 5;	// invalid
	case 0xE8: return 2;
	case 0xE9: return 2;
	case 0xEA: return 2;
//	case 0xEB: return 2;	// invalid
	case 0xEC: return 4;
	case 0xED: return 4;
	case 0xEE: return 6;
//	case 0xEF: return 6;	// invalid
	case 0xF0: return 2;
	case 0xF1: return 5;
//	case 0xF2: return 2;	// invalid
//	case 0xF3: return 8;	// invalid
//	case 0xF4: return 4;	// invalid
	case 0xF5: return 4;
	case 0xF6: return 6;
//	case 0xF7: return 6;	// invalid
	case 0xF8: return 2;
	case 0xF9: return 4;
//	case 0xFA: return 2;	// invalid
//	case 0xFB: return 7;	// invalid
//	case 0xFC: return 4;	// invalid
	case 0xFD: return 4;
	case 0xFE: return 7;
//	case 0xFF: return 7;	// invalid
	}

	return 0;	//	Return zero if instruction is not implemented in the SAP6502
}


#undef READ
#undef WRITE
#undef HEATMAP_X


static DWORD InternalCpuExecute(const DWORD uTotalCycles, const bool bVideoUpdate)
{
	ProgramControlROM();
	ULONG uExecutedCycles = 0;
	ULONG uElapsedCycles = 0;

	if (g_nAppMode == MODE_RUNNING || g_nAppMode == MODE_BENCHMARK)
	{
		if (GetMainCpu() == CPU_6502) {
			do {
				uElapsedCycles = SAP6502Cycles();
				if (uElapsedCycles == 0) uElapsedCycles = Cpu6502(0, false);		// Apple ][, ][+, //e, Clones
				else EmulateSAP6502(uExecutedCycles);
				uExecutedCycles += uElapsedCycles;
//				CheckSynchronousInterruptSources(uElapsedCycles, uExecutedCycles);

				// NTSC_BEGIN
				if (bVideoUpdate)
				{
					NTSC_VideoUpdateCycles(uElapsedCycles);
				}
				// NTSC_END
				
			} while (uExecutedCycles < uTotalCycles);

		}
		else {
			uElapsedCycles = SAP6502Cycles();
			if (uElapsedCycles == 0) uElapsedCycles = Cpu65C02(0, false);		// Apple ][, ][+, //e, Clones
			else EmulateSAP6502(uExecutedCycles);
			uExecutedCycles += uElapsedCycles;
			//				CheckSynchronousInterruptSources(uElapsedCycles, uExecutedCycles);

							// NTSC_BEGIN
			if (bVideoUpdate)
			{
				NTSC_VideoUpdateCycles(uElapsedCycles);
			}
			// NTSC_END


//			return Cpu65C02(uTotalCycles, bVideoUpdate);	// Enhanced Apple //e
		}
	}
	else
	{
		_ASSERT(g_nAppMode == MODE_STEPPING || g_nAppMode == MODE_DEBUG);
		if (GetMainCpu() == CPU_6502)
			return Cpu6502_debug(uTotalCycles, bVideoUpdate);	// Apple ][, ][+, //e, Clones
		else
			return Cpu65C02_debug(uTotalCycles, bVideoUpdate);	// Enhanced Apple //e
	}
	return uExecutedCycles;
}

//
// ----- ALL GLOBALLY ACCESSIBLE FUNCTIONS ARE BELOW THIS LINE -----
//

//===========================================================================

// Called by z80_RDMEM()
BYTE CpuRead(USHORT addr, ULONG uExecutedCycles)
{
	if (g_nAppMode == MODE_RUNNING)
	{
		return _READ_WITH_IO_F8xx;	// Superset of _READ
	}

	return Heatmap_ReadByte_With_IO_F8xx(addr, uExecutedCycles);
}

// Called by z80_WRMEM()
void CpuWrite(USHORT addr, BYTE value, ULONG uExecutedCycles)
{
	if (g_nAppMode == MODE_RUNNING)
	{
		_WRITE_WITH_IO_F8xx(value);	// Superset of _WRITE
		return;
	}

	Heatmap_WriteByte_With_IO_F8xx(addr, value, uExecutedCycles);
}

//===========================================================================

// Description:
//	Call this when an IO-reg is accessed & accurate cycle info is needed
//  NB. Safe to call multiple times from the same IO function handler (as 'nExecutedCycles - g_nCyclesExecuted' will be zero the 2nd time)
// Pre:
//  nExecutedCycles = # of cycles executed by Cpu6502() or Cpu65C02() for this iteration of ContinueExecution()
// Post:
//	g_nCyclesExecuted
//	g_nCumulativeCycles
//
void CpuCalcCycles(const ULONG nExecutedCycles)
{
	// Calc # of cycles executed since this func was last called
	const ULONG nCycles = nExecutedCycles - g_nCyclesExecuted;
//	_ASSERT( (LONG)nCycles >= 0 );
	g_nCumulativeCycles += nCycles;

	g_nCyclesExecuted = nExecutedCycles;
}

//===========================================================================

// Old method with g_uInternalExecutedCycles runs faster!
//        Old     vs    New
// - 68.0,69.0MHz vs  66.7, 67.2MHz  (with check for VBL IRQ every opcode)
// - 89.6,88.9MHz vs  87.2, 87.9MHz  (without check for VBL IRQ)
// -                  75.9, 78.5MHz  (with check for VBL IRQ every 128 cycles)
// -                 137.9,135.6MHz  (with check for VBL IRQ & MB_Update every 128 cycles)

#if 0	// TODO: Measure perf increase by using this new method
ULONG CpuGetCyclesThisVideoFrame(ULONG)	// Old func using g_uInternalExecutedCycles
{
	CpuCalcCycles(g_uInternalExecutedCycles);
	return g_dwCyclesThisFrame + g_nCyclesExecuted;
}
#else
ULONG CpuGetCyclesThisVideoFrame(const ULONG nExecutedCycles)
{
	CpuCalcCycles(nExecutedCycles);
	return g_dwCyclesThisFrame + g_nCyclesExecuted;
}
#endif

//===========================================================================

DWORD CpuExecute(const DWORD uCycles, const bool bVideoUpdate)
{
#ifdef LOG_PERF_TIMINGS
	extern UINT64 g_timeCpu;
	PerfMarker perfMarker(g_timeCpu);
#endif

	g_nCyclesExecuted =	0;
	g_interruptInLastExecutionBatch = false;

#ifdef _DEBUG
	MB_CheckCumulativeCycles();
#endif

	// uCycles:
	//  =0  : Do single step
	//  >0  : Do multi-opcode emulation
	const DWORD uExecutedCycles = InternalCpuExecute(uCycles, bVideoUpdate);

	// Update 6522s (NB. Do this before updating g_nCumulativeCycles below)
	// . Ensures that 6522 regs are up-to-date for any potential save-state
	// . SyncEvent will trigger the 6522 TIMER1/2 underflow on the correct cycle
	MB_UpdateCycles(uExecutedCycles);

	const UINT nRemainingCycles = uExecutedCycles - g_nCyclesExecuted;
	g_nCumulativeCycles	+= nRemainingCycles;

	return uExecutedCycles;
}

//===========================================================================

// Called by:
// . CpuInitialize()
// . SY6522.Reset()
void CpuCreateCriticalSection(void)
{
	if (!g_bCritSectionValid)
	{
		InitializeCriticalSection(&g_CriticalSection);
		g_bCritSectionValid = true;
	}
}

//===========================================================================

// Called from RepeatInitialization():
// . MemInitialize() -> MemReset()
void CpuInitialize(void)
{
	regs.a = regs.x = regs.y = 0xFF;
	regs.sp = 0x01FF;

	CpuReset();

	CpuCreateCriticalSection();

	CpuIrqReset();
	CpuNmiReset();

	z80mem_initialize();
	z80_reset();
}

//===========================================================================

void CpuDestroy()
{
	if (g_bCritSectionValid)
	{
		DeleteCriticalSection(&g_CriticalSection);
		g_bCritSectionValid = false;
	}
}

//===========================================================================

void CpuReset()
{
	_ASSERT(mem != NULL);

	// 7 cycles
	regs.ps = (regs.ps | AF_INTERRUPT) & ~AF_DECIMAL;
	regs.pc = *(WORD*)(mem + 0xFFFC);
	regs.sp = 0x0100 | ((regs.sp - 3) & 0xFF);

	regs.bJammed = 0;

	g_irqDefer1Opcode = false;

	SetActiveCpu(GetMainCpu());
	z80_reset();
}

//===========================================================================

void CpuSetupBenchmark ()
{
	regs.a  = 0;
	regs.x  = 0;
	regs.y  = 0;
	regs.pc = 0x300;
	regs.sp = 0x1FF;

	// CREATE CODE SEGMENTS CONSISTING OF GROUPS OF COMMONLY-USED OPCODES
	{
		int addr   = 0x300;
		int opcode = 0;
		do
		{
			*(mem+addr++) = benchopcode[opcode];
			*(mem+addr++) = benchopcode[opcode];

			if (opcode >= SHORTOPCODES)
				*(mem+addr++) = 0;

			if ((++opcode >= BENCHOPCODES) || ((addr & 0x0F) >= 0x0B))
			{
				*(mem+addr++) = 0x4C;
				*(mem+addr++) = (opcode >= BENCHOPCODES) ? 0x00 : ((addr >> 4)+1) << 4;
				*(mem+addr++) = 0x03;
				while (addr & 0x0F)
					++addr;
			}
		} while (opcode < BENCHOPCODES);
	}
}

//===========================================================================

void CpuIrqReset()
{
	_ASSERT(g_bCritSectionValid);
	if (g_bCritSectionValid) EnterCriticalSection(&g_CriticalSection);
	g_bmIRQ = 0;
	if (g_bCritSectionValid) LeaveCriticalSection(&g_CriticalSection);
}

void CpuIrqAssert(eIRQSRC Device)
{
	_ASSERT(g_bCritSectionValid);
	if (g_bCritSectionValid) EnterCriticalSection(&g_CriticalSection);
	g_bmIRQ |= 1<<Device;
	if (g_bCritSectionValid) LeaveCriticalSection(&g_CriticalSection);
}

void CpuIrqDeassert(eIRQSRC Device)
{
	_ASSERT(g_bCritSectionValid);
	if (g_bCritSectionValid) EnterCriticalSection(&g_CriticalSection);
	g_bmIRQ &= ~(1<<Device);
	if (g_bCritSectionValid) LeaveCriticalSection(&g_CriticalSection);
}

//===========================================================================

void CpuNmiReset()
{
	_ASSERT(g_bCritSectionValid);
	if (g_bCritSectionValid) EnterCriticalSection(&g_CriticalSection);
	g_bmNMI = 0;
	g_bNmiFlank = FALSE;
	if (g_bCritSectionValid) LeaveCriticalSection(&g_CriticalSection);
}

void CpuNmiAssert(eIRQSRC Device)
{
	_ASSERT(g_bCritSectionValid);
	if (g_bCritSectionValid) EnterCriticalSection(&g_CriticalSection);
	if (g_bmNMI == 0) // NMI line is just becoming active
	    g_bNmiFlank = TRUE;
	g_bmNMI |= 1<<Device;
	if (g_bCritSectionValid) LeaveCriticalSection(&g_CriticalSection);
}

void CpuNmiDeassert(eIRQSRC Device)
{
	_ASSERT(g_bCritSectionValid);
	if (g_bCritSectionValid) EnterCriticalSection(&g_CriticalSection);
	g_bmNMI &= ~(1<<Device);
	if (g_bCritSectionValid) LeaveCriticalSection(&g_CriticalSection);
}

//===========================================================================

#define SS_YAML_KEY_CPU_TYPE "Type"
#define SS_YAML_KEY_REGA "A"
#define SS_YAML_KEY_REGX "X"
#define SS_YAML_KEY_REGY "Y"
#define SS_YAML_KEY_REGP "P"
#define SS_YAML_KEY_REGS "S"
#define SS_YAML_KEY_REGPC "PC"
#define SS_YAML_KEY_CUMULATIVE_CYCLES "Cumulative Cycles"
#define SS_YAML_KEY_IRQ_DEFER_1_OPCODE "Defer IRQ By 1 Opcode"

#define SS_YAML_VALUE_6502 "6502"
#define SS_YAML_VALUE_65C02 "65C02"

static const std::string& CpuGetSnapshotStructName(void)
{
	static const std::string name("CPU");
	return name;
}

void CpuSaveSnapshot(YamlSaveHelper& yamlSaveHelper)
{
	regs.ps |= (AF_RESERVED | AF_BREAK);

	YamlSaveHelper::Label state(yamlSaveHelper, "%s:\n", CpuGetSnapshotStructName().c_str());	
	yamlSaveHelper.SaveString(SS_YAML_KEY_CPU_TYPE, GetMainCpu() == CPU_6502 ? SS_YAML_VALUE_6502 : SS_YAML_VALUE_65C02);
	yamlSaveHelper.SaveHexUint8(SS_YAML_KEY_REGA, regs.a);
	yamlSaveHelper.SaveHexUint8(SS_YAML_KEY_REGX, regs.x);
	yamlSaveHelper.SaveHexUint8(SS_YAML_KEY_REGY, regs.y);
	yamlSaveHelper.SaveHexUint8(SS_YAML_KEY_REGP, regs.ps);
	yamlSaveHelper.SaveHexUint8(SS_YAML_KEY_REGS, (BYTE) regs.sp);
	yamlSaveHelper.SaveHexUint16(SS_YAML_KEY_REGPC, regs.pc);
	yamlSaveHelper.SaveHexUint64(SS_YAML_KEY_CUMULATIVE_CYCLES, g_nCumulativeCycles);
	yamlSaveHelper.SaveBool(SS_YAML_KEY_IRQ_DEFER_1_OPCODE, g_irqDefer1Opcode);
}

void CpuLoadSnapshot(YamlLoadHelper& yamlLoadHelper, UINT version)
{
	if (!yamlLoadHelper.GetSubMap(CpuGetSnapshotStructName()))
		return;

	std::string cpuType = yamlLoadHelper.LoadString(SS_YAML_KEY_CPU_TYPE);
	eCpuType cpu;
	if (cpuType == SS_YAML_VALUE_6502) cpu = CPU_6502;
	else if (cpuType == SS_YAML_VALUE_65C02) cpu = CPU_65C02;
	else throw std::runtime_error("Load: Unknown main CPU type");
	SetMainCpu(cpu);

	regs.a  = (BYTE)     yamlLoadHelper.LoadUint(SS_YAML_KEY_REGA);
	regs.x  = (BYTE)     yamlLoadHelper.LoadUint(SS_YAML_KEY_REGX);
	regs.y  = (BYTE)     yamlLoadHelper.LoadUint(SS_YAML_KEY_REGY);
	regs.ps = (BYTE)     yamlLoadHelper.LoadUint(SS_YAML_KEY_REGP) | (AF_RESERVED | AF_BREAK);
	regs.sp = (USHORT) ((yamlLoadHelper.LoadUint(SS_YAML_KEY_REGS) & 0xff) | 0x100);
	regs.pc = (USHORT)   yamlLoadHelper.LoadUint(SS_YAML_KEY_REGPC);

	CpuIrqReset();
	CpuNmiReset();
	g_nCumulativeCycles = yamlLoadHelper.LoadUint64(SS_YAML_KEY_CUMULATIVE_CYCLES);

	if (version >= 5)
		g_irqDefer1Opcode = yamlLoadHelper.LoadBool(SS_YAML_KEY_IRQ_DEFER_1_OPCODE);

	yamlLoadHelper.PopMap();
}
