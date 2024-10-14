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

static __forceinline void Fetch(BYTE& iOpcode, ULONG uExecutedCycles)
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

#define		DRIVER			0
#define		LOAD			4
#define		CONSTRANT		8
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
#define		ALUADC			0x01
#define		ALUSBC			0x06

#define		WRITEEPROM		0

unsigned long long g_controlROM[0x20000];
int g_maxStep[256];
bool g_SAPInitialized;

#define READ _READ_WITH_IO_F8xx
#define WRITE(value) _WRITE_WITH_IO_F8xx(value)
#define HEATMAP_X(address)

unsigned long long EPROM[0x20000];

void WriteEPROM()
{
	if (!WRITEEPROM) return;
	for (int i = 0; i < 0x20000; i++) {
		EPROM[i] = g_controlROM[i] ^ 
			( UCOUNTERRESET | PCCLOCKLO	| PCCLOCKHI	| MEMACCESS	| MWRITE | PCSEL | UPDATEC | UPDATENZ | UPDATEV | FLAGINST | SHIFTRIGHT | SBC | BITOP );
		if ((g_controlROM[i] & PCSEL)) EPROM[i] |= PCSELBAR;
		if ((g_controlROM[i] & MWRITE)) EPROM[i] |= MREAD;
	}
	FILE* fp;
	for (int rom = 0; rom < 5; rom++) {
		char fname[40];
		sprintf_s(fname, "SAP6502_ROM%d.bin", rom);
		fopen_s(&fp, fname, "w+b");
		for (int i = 0; i < 0x20000; i++) {
			fputc ((EPROM[i] >> (rom * 8)) & 0xff, fp);
		}
		fclose (fp);
	}

}

void	SetMicroInstruction(int i, unsigned long long value)
{
	g_controlROM[(i + ((g_maxStep[i]) << 8))] = value;
	g_controlROM[FLAGBIT | (i + ((g_maxStep[i]) << 8))] = value;
	g_maxStep[i] ++;
}

void	SetMicroInstruction(int i, unsigned long long value, bool flag)
{
	g_controlROM[(flag ? FLAGBIT : 0x00) | (i + ((g_maxStep[i]) << 8))] = value;
	if (flag) g_maxStep[i] ++;
}

void ProgramRESET()
{
	for (int instruction = 0; instruction < 0x100; instruction++) {
		g_maxStep[instruction] = 24;
		SetMicroInstruction(instruction, (EAL << LOAD) | (CONSTR << DRIVER) | (0x0c << CONSTRANT));						//	EAL = 0xfc
		SetMicroInstruction(instruction, (EAH << LOAD) | (CONSTR << DRIVER) | (0x0f << CONSTRANT));						//	EAH = 0xff
		SetMicroInstruction(instruction, (PCL << LOAD) | MEMACCESS | PCSEL);										    //	Read PCL
		SetMicroInstruction(instruction, (EAL << LOAD) | (CONSTR << DRIVER) | (0x0d << CONSTRANT));						//	EAL = 0xfd
		SetMicroInstruction(instruction, (PCH << LOAD) | MEMACCESS | PCSEL);										    //	Read PCH
		SetMicroInstruction(instruction, (SPREG << LOAD) | (CONSTR << DRIVER) | (0x0f << CONSTRANT) | UCOUNTERRESET);	//	Read SPREG = 0xff
	}
}


void ProgramREL(int instruction)
{
	SetMicroInstruction(instruction, (BREG << LOAD) | PCCLOCKLO | PCCLOCKHI | MEMACCESS | PCSEL);	//	Read EAL
	SetMicroInstruction(instruction, (EAL << LOAD) | (ALU << DRIVER) | (ALUBREG << ALUOP) | (UFLAG << FLAGSELECT));
	SetMicroInstruction(instruction, (EAH << LOAD) | (CONSTR << DRIVER) | (0 << CONSTRANT), 0);	//	Read EAL
	SetMicroInstruction(instruction, (EAH << LOAD) | (CONSTR << DRIVER) | (0x0f << CONSTRANT), 1);	//	Read EAL
}

void ProgramIMM(int instruction)
{
	SetMicroInstruction(instruction, (EAL << LOAD) | (PCL << DRIVER) | PCSEL);							//	Read EAL
	SetMicroInstruction(instruction, (EAH << LOAD) | (PCH << DRIVER) | PCCLOCKLO | PCCLOCKHI | PCSEL);	//	Read EAL
}

void ProgramZPG(int instruction)
{
	SetMicroInstruction(instruction, (EAL << LOAD) | PCCLOCKLO | PCCLOCKHI | MEMACCESS | PCSEL);	//	Read EAL
	SetMicroInstruction(instruction, (EAH << LOAD) | (CONSTR << DRIVER));								//	Set EAH = 0;
}

void ProgramZPX(int instruction)
{
	SetMicroInstruction(instruction, (AH << LOAD) | PCCLOCKLO | PCCLOCKHI | MEMACCESS | PCSEL);		//	BREG <- MEM[PC]
	SetMicroInstruction(instruction, (BREG << LOAD) | (XREG << DRIVER));									//	AH <- XREG
	SetMicroInstruction(instruction, (EAL << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | CARRYZERO);	//	Set EAL = 0;
	SetMicroInstruction(instruction, (EAH << LOAD) | (CONSTR << DRIVER));								//	Set EAH = 0;
}

void ProgramZPY(int instruction)
{
	SetMicroInstruction(instruction, (AH << LOAD) | PCCLOCKLO | PCCLOCKHI | MEMACCESS | PCSEL);	//	BREG <- Read
	SetMicroInstruction(instruction, (BREG << LOAD) | (YREG << DRIVER));								//	AH <- XREG
	SetMicroInstruction(instruction, (EAL << LOAD) | (ALU << DRIVER) | (3 << ALUOP) | NOBCD | CARRYZERO);		//	Set EAH = 0;
	SetMicroInstruction(instruction, (EAH << LOAD) | (CONSTR << DRIVER));		 						//	Set EAH = 0;
}

void ProgramABS(int instruction)
{
	SetMicroInstruction(instruction, (EAL << LOAD) | PCCLOCKLO | PCCLOCKHI | MEMACCESS | PCSEL);								//	Read EAL
	SetMicroInstruction(instruction, (EAH << LOAD) | PCCLOCKLO | PCCLOCKHI | MEMACCESS | PCSEL);								//	Read EAH;
}

void ProgramABX(int instruction)
{
	SetMicroInstruction(instruction, (AH << LOAD) | PCCLOCKLO | PCCLOCKHI | MEMACCESS | PCSEL);								//	Read EAL
	SetMicroInstruction(instruction, (EAH << LOAD) | PCCLOCKLO | PCCLOCKHI | MEMACCESS | PCSEL);								//	Read EAH;
	SetMicroInstruction(instruction, (BREG << LOAD) | (XREG << DRIVER));
	SetMicroInstruction(instruction, (EAL << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | CARRYZERO | (PFLAG << FLAGSELECT));		//	Add IX to EAL

	//	Need to have a different pathway for different flag values
	SetMicroInstruction(instruction, (PFLAG << FLAGSELECT), 0);
	SetMicroInstruction(instruction, (BREG << LOAD) | (EAH << DRIVER) | (PFLAG << FLAGSELECT), 1);

	SetMicroInstruction(instruction, (PFLAG << FLAGSELECT), 0);
	SetMicroInstruction(instruction, (AH << LOAD) | (CONSTR << DRIVER) | (1 << CONSTRANT) | (PFLAG << FLAGSELECT), 1);

	SetMicroInstruction(instruction, (PFLAG << FLAGSELECT), 0);	//	Read EAH;
	SetMicroInstruction(instruction, (EAH << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | CARRYZERO, 1);
}

void ProgramABY(int instruction)
{
	SetMicroInstruction(instruction, (AH << LOAD) | PCCLOCKLO | PCCLOCKHI | MEMACCESS | PCSEL);	//	Read EAL
	SetMicroInstruction(instruction, (EAH << LOAD) | PCCLOCKLO | PCCLOCKHI | MEMACCESS | PCSEL);	//	Read EAH;
	SetMicroInstruction(instruction, (BREG << LOAD) | (YREG << DRIVER));
	SetMicroInstruction(instruction, (EAL << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | CARRYZERO | (PFLAG << FLAGSELECT));		//	Set EAH = 0;

	//	Need to have a different pathway for different flag values
	SetMicroInstruction(instruction, (PFLAG << FLAGSELECT), 0);	//	Read EAH;
	SetMicroInstruction(instruction, (BREG << LOAD) | (EAH << DRIVER) | (PFLAG << FLAGSELECT), 1);

	SetMicroInstruction(instruction, (PFLAG << FLAGSELECT), 0);	//	Read EAH;
	SetMicroInstruction(instruction, (AH << LOAD) | (CONSTR << DRIVER) | (1 << CONSTRANT) | (PFLAG << FLAGSELECT), 1);

	SetMicroInstruction(instruction, (PFLAG << FLAGSELECT), 0);	//	Read EAH;
	SetMicroInstruction(instruction, (EAH << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | CARRYZERO, 1);		//	Set EAH = 0;
}

void ProgramXID(int instruction)
{
	SetMicroInstruction(instruction, (BREG << LOAD) | PCCLOCKLO | PCCLOCKHI | MEMACCESS | PCSEL);	//	Read ZPG
	SetMicroInstruction(instruction, (AH << LOAD) | (XREG << DRIVER));
	SetMicroInstruction(instruction, (EAL << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | CARRYZERO);		//	ADD ZPG + XID;
	SetMicroInstruction(instruction, (EAH << LOAD) | (CONSTR << DRIVER));								//	Set EAH = 0;

	SetMicroInstruction(instruction, (EBL << LOAD) | MEMACCESS | EASEL);
	SetMicroInstruction(instruction, (BREG << LOAD) | (EAL << DRIVER) | EASEL);
	SetMicroInstruction(instruction, (AH << LOAD) | (CONSTR << DRIVER) | (1 << CONSTRANT));
	SetMicroInstruction(instruction, (EAL << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | CARRYZERO);		//	ADD ZPG + XID;
	SetMicroInstruction(instruction, (EAH << LOAD) | MEMACCESS | EASEL);
	SetMicroInstruction(instruction, (EAL << LOAD) | (EBL << DRIVER));
}

void ProgramYID(int instruction)
{
	//	Read Zero page address 00XX into EBL
	SetMicroInstruction(instruction, (EAL << LOAD) | PCCLOCKLO | PCCLOCKHI | MEMACCESS | PCSEL);	//	Read ZPG
	SetMicroInstruction(instruction, (EAH << LOAD) | (CONSTR << DRIVER));								//	Set EAH = 0;
	SetMicroInstruction(instruction, (EBL << LOAD) | MEMACCESS | EASEL);							//	Load ZPG into EBL

	//	Add 1 to eal
	SetMicroInstruction(instruction, (BREG << LOAD) | (EAL << DRIVER) | EASEL);						//	Inc EAL
	SetMicroInstruction(instruction, (AH << LOAD) | (CONSTR << DRIVER) | (1 << CONSTRANT));
	SetMicroInstruction(instruction, (EAL << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | CARRYZERO);		//	

	//	Read 00(XX+1) into EAH
	SetMicroInstruction(instruction, (EAH << LOAD) | MEMACCESS | EASEL);							//	load ZPG+1 into EAH

	SetMicroInstruction(instruction, (BREG << LOAD) | (EBL << DRIVER));
	SetMicroInstruction(instruction, (AH << LOAD) | (YREG << DRIVER));
	SetMicroInstruction(instruction, (EAL << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | CARRYZERO | (PFLAG << FLAGSELECT));		//	ADD ZPG + XID;

		//	Need to have a different pathway for different flag values
	SetMicroInstruction(instruction, (PFLAG << FLAGSELECT), 0);	//	Read EAH;
	SetMicroInstruction(instruction, (BREG << LOAD) | (EAH << DRIVER) | (PFLAG << FLAGSELECT), 1);

	SetMicroInstruction(instruction, (PFLAG << FLAGSELECT), 0);	//	Read EAH;
	SetMicroInstruction(instruction, (AH << LOAD) | (CONSTR << DRIVER) | (1 << CONSTRANT) | (PFLAG << FLAGSELECT), 1);

	SetMicroInstruction(instruction, (PFLAG << FLAGSELECT), 0);	//	Read EAH;
	SetMicroInstruction(instruction, (EAH << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | CARRYZERO, 1);		//	Set EAH = 0;
}


//	Flow control
void ProgramRESET(int instruction)
{
	SetMicroInstruction(instruction, (PCL << LOAD) | (CONSTR << DRIVER) | (0x0c << CONSTRANT));
	SetMicroInstruction(instruction, (PCH << LOAD) | (CONSTR << DRIVER) | (0x0f << CONSTRANT));

	SetMicroInstruction(instruction, (EBL << LOAD) | PCCLOCKLO | PCCLOCKHI | MEMACCESS | PCSEL);	//	Read EAL
	SetMicroInstruction(instruction, (PCH << LOAD) | MEMACCESS | PCSEL);	//	Read EAH;
	SetMicroInstruction(instruction, (PCL << LOAD) | (EBL << DRIVER) | UCOUNTERRESET);	//	Read EAL
}
//	Flow control
void ProgramJMP(int instruction)
{
	SetMicroInstruction(instruction, (EBL << LOAD) | PCCLOCKLO | PCCLOCKHI | MEMACCESS | PCSEL);	//	Read EAL
	SetMicroInstruction(instruction, (PCH << LOAD) | MEMACCESS | PCSEL);	//	Read EAH;
	SetMicroInstruction(instruction, (PCL << LOAD) | (EBL << DRIVER) | UCOUNTERRESET);	//	Read EAL
}

//	Flow control
void ProgramJMPI(int instruction)
{
	SetMicroInstruction(instruction, (EBL << LOAD) | PCCLOCKLO | PCCLOCKHI | MEMACCESS | PCSEL);	//	Read EAL
	SetMicroInstruction(instruction, (PCH << LOAD) | MEMACCESS | PCSEL);	//	Read EAH;
	SetMicroInstruction(instruction, (PCL << LOAD) | (EBL << DRIVER));	//	Read EAL

	SetMicroInstruction(instruction, (EBL << LOAD) | PCCLOCKLO | PCCLOCKHI | MEMACCESS | PCSEL);	//	Read EAL
	SetMicroInstruction(instruction, (PCH << LOAD) | MEMACCESS | PCSEL);	//	Read EAH;
	SetMicroInstruction(instruction, (PCL << LOAD) | (EBL << DRIVER) | UCOUNTERRESET);	//	Read EAL
}



void ProgramJSR(int instruction)
{
	SetMicroInstruction(instruction, (EBL << LOAD) | PCCLOCKLO | PCCLOCKHI | MEMACCESS | PCSEL);	//	Read EAL

	SetMicroInstruction(instruction, (EAL << LOAD) | (SPREG << DRIVER));	//	Read EAL
	SetMicroInstruction(instruction, (EAH << LOAD) | (CONSTR << DRIVER) | (1 << CONSTRANT));
	SetMicroInstruction(instruction, (EBH << LOAD) | (PCH << DRIVER) | PCSEL);
	SetMicroInstruction(instruction, (EBH << DRIVER) | MEMACCESS | MWRITE | EASEL);

	SetMicroInstruction(instruction, (BREG << LOAD) | (SPREG << DRIVER));	//	Read EAL
	SetMicroInstruction(instruction, (AH << LOAD) | (CONSTR << DRIVER) | (0x0f << CONSTRANT));							//	Read EAL
	SetMicroInstruction(instruction, (EAL << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | CARRYZERO);		//	Set EAH = 0;

	SetMicroInstruction(instruction, (EBH << LOAD) | (PCL << DRIVER) | PCSEL);
	SetMicroInstruction(instruction, (EBH << DRIVER) | MEMACCESS | MWRITE | EASEL);
	SetMicroInstruction(instruction, (BREG << LOAD) | (EAL << DRIVER));	//	Read EAL
	SetMicroInstruction(instruction, (SPREG << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | CARRYZERO);		//	Set EAH = 0;

	SetMicroInstruction(instruction, (PCH << LOAD) | MEMACCESS | PCSEL);	//	Read EAL
	SetMicroInstruction(instruction, (PCL << LOAD) | (EBL << DRIVER) | UCOUNTERRESET);	//	Read EAL
}

void ProgramRTS(int instruction)
{
	SetMicroInstruction(instruction, (BREG << LOAD) | (SPREG << DRIVER));	//	Read EAL
	SetMicroInstruction(instruction, (AH << LOAD) | (CONSTR << DRIVER) | (0x01 << CONSTRANT));							//	Read EAL
	SetMicroInstruction(instruction, (EAL << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | CARRYZERO);		//	Set EAH = 0;
	SetMicroInstruction(instruction, (EAH << LOAD) | (CONSTR << DRIVER) | (1 << CONSTRANT));
	SetMicroInstruction(instruction, (PCL << LOAD) | MEMACCESS | EASEL);								//	Load PCL	

	SetMicroInstruction(instruction, (BREG << LOAD) | (EAL << DRIVER));	//	Read EAL
	SetMicroInstruction(instruction, (EAL << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | CARRYZERO);		//	Set EAH = 0;
	SetMicroInstruction(instruction, (PCH << LOAD) | MEMACCESS | EASEL);								//	Load PCH

	SetMicroInstruction(instruction, (SPREG << LOAD) | (EAL << DRIVER) | PCCLOCKLO | PCCLOCKHI | UCOUNTERRESET);			//	Read EAL
}


void ProgramBranch(int instruction, int checkFlag, bool branchIf)
{
	//	Starts at uCount = 4 
	SetMicroInstruction(instruction, (ALU << LOAD) | (STREG << DRIVER) | (checkFlag << FLAGSELECT));

	//	Check Branch Condition
	if (branchIf) {
		SetMicroInstruction(instruction, (ALU << LOAD) | (ALU << DRIVER) | PCSEL | UCOUNTERRESET, 0);	//	Read EAL
		SetMicroInstruction(instruction, (AH << LOAD) | (PCL << DRIVER) | PCSEL, 1);
	}
	else {
		SetMicroInstruction(instruction, (AH << LOAD) | (PCL << DRIVER) | PCSEL, 0);
		SetMicroInstruction(instruction, (ALU << LOAD) | (ALU << DRIVER) | PCSEL | UCOUNTERRESET, 1);
	}

	//	Need two pathways, one for a positive offset and one for a negative offset

	SetMicroInstruction(instruction, (PCL << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | CARRYZERO | (PFLAG << FLAGSELECT));

	SetMicroInstruction(instruction, (BREG << LOAD) | (EAH << DRIVER) | (PFLAG << FLAGSELECT), 0);
	SetMicroInstruction(instruction, (BREG << LOAD) | (EAH << DRIVER) | (PFLAG << FLAGSELECT), 1);

	SetMicroInstruction(instruction, (AH << LOAD) | (PCH << DRIVER) | (PFLAG << FLAGSELECT), 0);
	SetMicroInstruction(instruction, (AH << LOAD) | (PCH << DRIVER) | (PFLAG << FLAGSELECT), 1);

	SetMicroInstruction(instruction, (PCH << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | UCOUNTERRESET | CARRYZERO, 0);
	SetMicroInstruction(instruction, (PCH << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | UCOUNTERRESET | CARRYONE, 1);
}

//	Stack Ops
void ProgramPHA(int instruction)
{
	SetMicroInstruction(instruction, (EAL << LOAD) | (SPREG << DRIVER));	//	Read EAL
	SetMicroInstruction(instruction, (EAH << LOAD) | (CONSTR << DRIVER) | (1 << CONSTRANT));
	SetMicroInstruction(instruction, (AREG << DRIVER) | MEMACCESS | MWRITE | EASEL);

	SetMicroInstruction(instruction, (BREG << LOAD) | (SPREG << DRIVER));	//	Read EAL
	SetMicroInstruction(instruction, (AH << LOAD) | (CONSTR << DRIVER) | (0x0f << CONSTRANT));							//	Read EAL
	SetMicroInstruction(instruction, (SPREG << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | CARRYZERO | UCOUNTERRESET);		//	Set EAH = 0;
}

void ProgramPHP(int instruction)
{
	SetMicroInstruction(instruction, (EAL << LOAD) | (SPREG << DRIVER));	//	Read EAL
	SetMicroInstruction(instruction, (EAH << LOAD) | (CONSTR << DRIVER) | (1 << CONSTRANT));
	SetMicroInstruction(instruction, (STREG << DRIVER) | MEMACCESS | MWRITE | EASEL);

	SetMicroInstruction(instruction, (BREG << LOAD) | (SPREG << DRIVER));	//	Read EAL
	SetMicroInstruction(instruction, (AH << LOAD) | (CONSTR << DRIVER) | (0x0f << CONSTRANT));							//	Read EAL
	SetMicroInstruction(instruction, (SPREG << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | CARRYZERO | UCOUNTERRESET);		//	Set EAH = 0;
}


void ProgramPLA(int instruction)
{
	SetMicroInstruction(instruction, (BREG << LOAD) | (SPREG << DRIVER));											//	Read EAL
	SetMicroInstruction(instruction, (AH << LOAD) | (CONSTR << DRIVER) | (0x01 << CONSTRANT));						//	Read EAL
	SetMicroInstruction(instruction, (SPREG << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | CARRYZERO);		//	Set EAH = 0;

	SetMicroInstruction(instruction, (EAL << LOAD) | (SPREG << DRIVER));											//	Read EAL
	SetMicroInstruction(instruction, (EAH << LOAD) | (CONSTR << DRIVER) | (1 << CONSTRANT));
	SetMicroInstruction(instruction, (BREG << LOAD) | MEMACCESS | EASEL);										//	Read EAL
	SetMicroInstruction(instruction, (AREG << LOAD) | (ALU << DRIVER) | (ALUBREG << ALUOP) | UPDATENZ | UCOUNTERRESET);		//	Read EAL
}

void ProgramPLP(int instruction)
{
	SetMicroInstruction(instruction, (BREG << LOAD) | (SPREG << DRIVER));	//	Read EAL
	SetMicroInstruction(instruction, (AH << LOAD) | (CONSTR << DRIVER) | (0x01 << CONSTRANT));							//	Read EAL
	SetMicroInstruction(instruction, (SPREG << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | CARRYZERO);		//	Set EAH = 0;

	SetMicroInstruction(instruction, (EAL << LOAD) | (SPREG << DRIVER));	//	Read EAL
	SetMicroInstruction(instruction, (EAH << LOAD) | (CONSTR << DRIVER) | (1 << CONSTRANT));
	SetMicroInstruction(instruction, (STREG << LOAD) | MEMACCESS | EASEL | UCOUNTERRESET);							//	Read EAL
}

void ProgramNOP(int instruction)
{
	SetMicroInstruction(instruction, (STREG << LOAD) | (STREG << DRIVER) | UCOUNTERRESET);
}


//	ALU Operations
void ProgramDEC(int instruction)
{
	SetMicroInstruction(instruction, (BREG << LOAD) | MEMACCESS | EASEL);							//	Read EAL
	SetMicroInstruction(instruction, (AH << LOAD) | (CONSTR << DRIVER) | (0x0f << CONSTRANT));				//	Read EAL
	SetMicroInstruction(instruction, (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | UPDATENZ | CARRYZERO | MEMACCESS | MWRITE | EASEL | UCOUNTERRESET);							//	Read EAL
}

void ProgramDEX(int instruction)
{
	SetMicroInstruction(instruction, (BREG << LOAD) | (XREG << DRIVER));							//	Read EAL
	SetMicroInstruction(instruction, (AH << LOAD) | (CONSTR << DRIVER) | (0x0f << CONSTRANT));				//	Read EAL
	SetMicroInstruction(instruction, (XREG << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | UPDATENZ | CARRYZERO | UCOUNTERRESET);							//	Read EAL
}

void ProgramDEY(int instruction)
{
	SetMicroInstruction(instruction, (BREG << LOAD) | (YREG << DRIVER));							//	Read EAL
	SetMicroInstruction(instruction, (AH << LOAD) | (CONSTR << DRIVER) | (0x0f << CONSTRANT));				//	Read EAL
	SetMicroInstruction(instruction, (YREG << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | UPDATENZ | CARRYZERO | UCOUNTERRESET);							//	Read EAL
}

void ProgramINC(int instruction)
{
	SetMicroInstruction(instruction, (BREG << LOAD) | MEMACCESS | EASEL);							//	Read EAL
	SetMicroInstruction(instruction, (AH << LOAD) | (CONSTR << DRIVER) | (1 << CONSTRANT));				//	Read EAL
	SetMicroInstruction(instruction, (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | UPDATENZ | CARRYZERO | MEMACCESS | MWRITE | EASEL | UCOUNTERRESET);							//	Read EAL
}

void ProgramINX(int instruction)
{
	SetMicroInstruction(instruction, (BREG << LOAD) | (XREG << DRIVER));							//	Read EAL
	SetMicroInstruction(instruction, (AH << LOAD) | (CONSTR << DRIVER) | (1 << CONSTRANT));				//	Read EAL
	SetMicroInstruction(instruction, (XREG << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | UPDATENZ | CARRYZERO | UCOUNTERRESET);							//	Read EAL
}

void ProgramINY(int instruction)
{
	SetMicroInstruction(instruction, (BREG << LOAD) | (YREG << DRIVER));							//	Read EAL
	SetMicroInstruction(instruction, (AH << LOAD) | (CONSTR << DRIVER) | (1 << CONSTRANT));				//	Read EAL
	SetMicroInstruction(instruction, (YREG << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | UPDATENZ | CARRYZERO | UCOUNTERRESET);							//	Read EAL
}

void ProgramADC(int instruction)
{
	SetMicroInstruction(instruction, (BREG << LOAD) | MEMACCESS | EASEL);							//	Read EAL
	SetMicroInstruction(instruction, (AH << LOAD) | (AREG << DRIVER));							//	Read EAL
	SetMicroInstruction(instruction, (AREG << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | UPDATENZ | UPDATEC | UPDATEV | UCOUNTERRESET);							//	Read EAL
}

void ProgramAND(int instruction)
{
	SetMicroInstruction(instruction, (BREG << LOAD) | MEMACCESS | EASEL);							//	Read EAL
	SetMicroInstruction(instruction, (AH << LOAD) | (AREG << DRIVER));							//	Read EAL
	SetMicroInstruction(instruction, (AREG << LOAD) | (ALU << DRIVER) | (ALUAND << ALUOP) | UPDATENZ | UCOUNTERRESET);							//	Read EAL
}

void ProgramBIT(int instruction)
{
	SetMicroInstruction(instruction, (BREG << LOAD) | MEMACCESS | EASEL);							//	Read EAL
	SetMicroInstruction(instruction, (AH << LOAD) | (AREG << DRIVER));							//	Read EAL
	SetMicroInstruction(instruction, (ALU << LOAD) | (ALU << DRIVER) | (ALUAND << ALUOP) | UPDATENZ | UPDATEV | UCOUNTERRESET | BITOP);							//	Read EAL
}


void ProgramASL(int instruction)
{
	SetMicroInstruction(instruction, (EBL << LOAD) | MEMACCESS | EASEL);							//	Read EAL
	SetMicroInstruction(instruction, (BREG << LOAD) | (EBL << DRIVER));							//	Read EAL
	SetMicroInstruction(instruction, (AH << LOAD) | (EBL << DRIVER));
	SetMicroInstruction(instruction, (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | UPDATENZ | UPDATEC | CARRYZERO | MEMACCESS | MWRITE | EASEL | UCOUNTERRESET);							//	Read EAL
}

void ProgramASLA(int instruction)
{
	SetMicroInstruction(instruction, (AH << LOAD) | (AREG << DRIVER));							//	Read EAL
	SetMicroInstruction(instruction, (BREG << LOAD) | (AREG << DRIVER));
	SetMicroInstruction(instruction, (AREG << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | UPDATENZ | UPDATEC | CARRYZERO | UCOUNTERRESET);							//	Read EAL
}

void ProgramROL(int instruction)
{
	SetMicroInstruction(instruction, (EBL << LOAD) | MEMACCESS | EASEL);							//	Read EAL
	SetMicroInstruction(instruction, (BREG << LOAD) | (EBL << DRIVER));							//	Read EAL
	SetMicroInstruction(instruction, (AH << LOAD) | (EBL << DRIVER));
	SetMicroInstruction(instruction, (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | UPDATENZ | UPDATEC | MEMACCESS | MWRITE | EASEL | UCOUNTERRESET);							//	Read EAL
}

void ProgramROLA(int instruction)
{
	SetMicroInstruction(instruction, (AH << LOAD) | (AREG << DRIVER));							//	Read EAL
	SetMicroInstruction(instruction, (BREG << LOAD) | (AREG << DRIVER));
	SetMicroInstruction(instruction, (AREG << LOAD) | (ALU << DRIVER) | (ALUADC << ALUOP) | NOBCD | UPDATENZ | UPDATEC | UCOUNTERRESET);							//	Read EAL
}

void ProgramLSR(int instruction)
{
	SetMicroInstruction(instruction, (BREG << LOAD) | MEMACCESS | EASEL);							//	Read EAL
	SetMicroInstruction(instruction, (ALU << DRIVER) | (ALUBREG << ALUOP) | UPDATENZ | UPDATEC | CARRYZERO | MEMACCESS | MWRITE | EASEL | UCOUNTERRESET | SHIFTRIGHT);							//	Read EAL
}

void ProgramLSRA(int instruction)
{
	SetMicroInstruction(instruction, (BREG << LOAD) | (AREG << DRIVER));							//	Read EAL
	SetMicroInstruction(instruction, (AREG << LOAD) | (ALU << DRIVER) | (ALUBREG << ALUOP) | UPDATENZ | UPDATEC | CARRYZERO | UCOUNTERRESET | SHIFTRIGHT);							//	Read EAL
}

void ProgramROR(int instruction)
{
	SetMicroInstruction(instruction, (BREG << LOAD) | MEMACCESS | EASEL);							//	Read EAL
	SetMicroInstruction(instruction, (ALU << DRIVER) | (ALUBREG << ALUOP) | UPDATENZ | UPDATEC | MEMACCESS | MWRITE | EASEL | UCOUNTERRESET | SHIFTRIGHT);							//	Read EAL
}

void ProgramRORA(int instruction)
{
	SetMicroInstruction(instruction, (BREG << LOAD) | (AREG << DRIVER));
	SetMicroInstruction(instruction, (AREG << LOAD) | (ALU << DRIVER) | (ALUBREG << ALUOP) | UPDATENZ | UPDATEC | UCOUNTERRESET | SHIFTRIGHT);							//	Read EAL
}

void ProgramCMP(int instruction)
{
	SetMicroInstruction(instruction, (BREG << LOAD) | MEMACCESS | EASEL);
	SetMicroInstruction(instruction, (AH << LOAD) | (AREG << DRIVER));
	SetMicroInstruction(instruction, (EBL << LOAD) | (ALU << DRIVER) | (ALUSBC << ALUOP) | NOBCD | UPDATENZ | UPDATEC | CARRYONE | UCOUNTERRESET);							//	Read EAL
}

void ProgramCPX(int instruction)
{
	SetMicroInstruction(instruction, (BREG << LOAD) | MEMACCESS | EASEL);							//	Read EAL
	SetMicroInstruction(instruction, (AH << LOAD) | (XREG << DRIVER));								//	Read EAL
	SetMicroInstruction(instruction, (ALU << LOAD) | (ALU << DRIVER) | (ALUSBC << ALUOP) | NOBCD | UPDATENZ | UPDATEC | CARRYONE | UCOUNTERRESET);							//	Read EAL
}

void ProgramCPY(int instruction)
{
	SetMicroInstruction(instruction, (BREG << LOAD) | MEMACCESS | EASEL);							//	Read EAL
	SetMicroInstruction(instruction, (AH << LOAD) | (YREG << DRIVER));								//	Read EAL
	SetMicroInstruction(instruction, (ALU << LOAD) | (ALU << DRIVER) | (ALUSBC << ALUOP) | NOBCD | UPDATENZ | UPDATEC | CARRYONE | UCOUNTERRESET);							//	Read EAL
}

void ProgramEOR(int instruction)
{
	SetMicroInstruction(instruction, (BREG << LOAD) | MEMACCESS | EASEL);
	SetMicroInstruction(instruction, (AH << LOAD) | (AREG << DRIVER));
	SetMicroInstruction(instruction, (AREG << LOAD) | (ALU << DRIVER) | (ALUXOR << ALUOP) | UPDATENZ | UCOUNTERRESET);
}

void ProgramORA(int instruction)
{
	SetMicroInstruction(instruction, (BREG << LOAD) | MEMACCESS | EASEL);
	SetMicroInstruction(instruction, (AH << LOAD) | (AREG << DRIVER));
	SetMicroInstruction(instruction, (AREG << LOAD) | (ALU << DRIVER) | (ALUORA << ALUOP) | UPDATENZ | UCOUNTERRESET);
}

void ProgramSBC(int instruction)
{
	SetMicroInstruction(instruction, (BREG << LOAD) | MEMACCESS | EASEL);
	SetMicroInstruction(instruction, (AH << LOAD) | (AREG << DRIVER));
	SetMicroInstruction(instruction, (AREG << LOAD) | (ALU << DRIVER) | (ALUSBC << ALUOP) | UPDATENZ | UPDATEC | UPDATEV | UCOUNTERRESET | SBC);
}

void ProgramLDA(int instruction)
{
	SetMicroInstruction(instruction, (BREG << LOAD) | MEMACCESS | EASEL);
	SetMicroInstruction(instruction, (AREG << LOAD) | (ALU << DRIVER) | (ALUBREG << ALUOP) | UPDATENZ | UCOUNTERRESET);
}

void ProgramLDX(int instruction)
{
	SetMicroInstruction(instruction, (BREG << LOAD) | MEMACCESS | EASEL);
	SetMicroInstruction(instruction, (XREG << LOAD) | (ALU << DRIVER) | (ALUBREG << ALUOP) | UPDATENZ | UCOUNTERRESET);
}

void ProgramLDY(int instruction)
{
	SetMicroInstruction(instruction, (BREG << LOAD) | MEMACCESS | EASEL);
	SetMicroInstruction(instruction, (YREG << LOAD) | (ALU << DRIVER) | (ALUBREG << ALUOP) | UPDATENZ | UCOUNTERRESET);
}

void ProgramSTA(int instruction)
{
	SetMicroInstruction(instruction, (AREG << DRIVER) | MEMACCESS | MWRITE | EASEL | UCOUNTERRESET);
}

void ProgramSTX(int instruction)
{
	SetMicroInstruction(instruction, (XREG << DRIVER) | MEMACCESS | MWRITE | EASEL | UCOUNTERRESET);
}

void ProgramSTY(int instruction)
{
	SetMicroInstruction(instruction, (YREG << DRIVER) | MEMACCESS | MWRITE | EASEL | UCOUNTERRESET);
}

void ProgramFLAGOP(int instruction)
{
	SetMicroInstruction(instruction, FLAGINST | UCOUNTERRESET);
}

void ProgramTAX(int instruction)
{
	SetMicroInstruction(instruction, (BREG << LOAD) | (AREG << DRIVER));
	SetMicroInstruction(instruction, (XREG << LOAD) | (ALU << DRIVER) | (ALUBREG << ALUOP) | UPDATENZ | UCOUNTERRESET);
}

void ProgramTAY(int instruction)
{
	SetMicroInstruction(instruction, (BREG << LOAD) | (AREG << DRIVER));
	SetMicroInstruction(instruction, (YREG << LOAD) | (ALU << DRIVER) | (ALUBREG << ALUOP) | UPDATENZ | UCOUNTERRESET);
}

void ProgramTSX(int instruction)
{
	SetMicroInstruction(instruction, (BREG << LOAD) | (SPREG << DRIVER));
	SetMicroInstruction(instruction, (XREG << LOAD) | (ALU << DRIVER) | (ALUBREG << ALUOP) | UPDATENZ | UCOUNTERRESET);
}

void ProgramTXA(int instruction)
{
	SetMicroInstruction(instruction, (BREG << LOAD) | (XREG << DRIVER));
	SetMicroInstruction(instruction, (AREG << LOAD) | (ALU << DRIVER) | (ALUBREG << ALUOP) | UPDATENZ | UCOUNTERRESET);
}

void ProgramTXS(int instruction)
{
	SetMicroInstruction(instruction, (SPREG << LOAD) | (XREG << DRIVER) | UCOUNTERRESET);
}

void ProgramTYA(int instruction)
{
	SetMicroInstruction(instruction, (BREG << LOAD) | (YREG << DRIVER));
	SetMicroInstruction(instruction, (AREG << LOAD) | (ALU << DRIVER) | (ALUBREG << ALUOP) | UPDATENZ | UCOUNTERRESET);
}


int		ProgramControlROM()
{
	int i;
	if (!g_SAPInitialized) {
		g_SAPInitialized = true;
	}
	else {
		return 0;
	}

	for (i = 0; i < 65536; i++) {
		g_controlROM[i] = 0x00;
	}
	//	Program in the fetch
	for (i = 0; i < 256; i++) {
		g_controlROM[FLAGBIT | i] = g_controlROM[i] = IREGLOAD | PCCLOCKLO | PCCLOCKHI | MEMACCESS | PCSEL;
		g_maxStep[i] = 1;
	}
	for (i = 0; i < 256; i++) {
		switch (i) {		// program each instruction

		//	Transfers
//		case 0x00:						ProgramBRK(i);					break;		/* BRK	*/
		case 0x10:	ProgramREL(i);		ProgramBranch(i, NFLAG, 0);		break;		/* BPL	*/
		case 0x20:						ProgramJSR(i);					break;		/* JSR	*/
		case 0x30:	ProgramREL(i);		ProgramBranch(i, NFLAG, 1);		break;		/* BMI	*/
//		case 0x40:						ProgramRTI(i);					break;		/* RTI	*/
		case 0x50:	ProgramREL(i);  	ProgramBranch(i, VFLAG, 0);		break;		/* BVC	*/
		case 0x60:						ProgramRTS(i);					break;		/* RTS	*/
		case 0x70:	ProgramREL(i);  	ProgramBranch(i, VFLAG, 1);		break;		/* BVS	*/
		case 0x90:	ProgramREL(i); 		ProgramBranch(i, CFLAG, 0);		break;		/* BCC	*/
		case 0xa0:	ProgramIMM(i);		ProgramLDY(i);					break;		/* LDY	*/
		case 0xb0:	ProgramREL(i);		ProgramBranch(i, CFLAG, 1);		break;		/* BCS	*/
		case 0xc0:	ProgramIMM(i);		ProgramCPY(i);					break;		/* CPY	*/
		case 0xd0:	ProgramREL(i);		ProgramBranch(i, ZFLAG, 0);		break;		/* BNE	*/
		case 0xe0:	ProgramIMM(i);		ProgramCPX(i);					break;		/* CPX	*/
		case 0xf0:	ProgramREL(i);		ProgramBranch(i, ZFLAG, 1);		break;		/* BEQ	*/

		case 0x01:	ProgramXID(i);		ProgramORA(i);					break;		/* ORA	*/
		case 0x11:	ProgramYID(i);		ProgramORA(i);					break;		/* ORA	*/
		case 0x21:	ProgramXID(i);		ProgramAND(i);					break;		/* AND	*/
		case 0x31:	ProgramYID(i);		ProgramAND(i);					break;		/* AND	*/
		case 0x41:	ProgramXID(i);		ProgramEOR(i);					break;		/* EOR	*/
		case 0x51:	ProgramYID(i);		ProgramEOR(i);					break;		/* EOR	*/
		case 0x61:	ProgramXID(i);		ProgramADC(i);					break;		/* ADC	*/
		case 0x71:	ProgramYID(i);		ProgramADC(i);					break;		/* ADC	*/
		case 0x81:	ProgramXID(i);		ProgramSTA(i);					break;		/* STA	*/
		case 0x91:	ProgramYID(i);		ProgramSTA(i);					break;		/* STA	*/
		case 0xa1:	ProgramXID(i);		ProgramLDA(i);					break;		/* LDA	*/
		case 0xb1:	ProgramYID(i);		ProgramLDA(i);					break;		/* LDA	*/
		case 0xc1:	ProgramXID(i);		ProgramCMP(i);					break;		/* CMP	*/
		case 0xd1:	ProgramYID(i);		ProgramCMP(i);					break;		/* CMP	*/
		case 0xe1:	ProgramXID(i);		ProgramSBC(i);					break;		/* SBC	*/
		case 0xf1:	ProgramYID(i);		ProgramSBC(i);					break;		/* SBC	*/

		case 0xa2:	ProgramIMM(i);		ProgramLDX(i);					break;		/* LDX	*/

		case 0x24:	ProgramZPG(i);		ProgramBIT(i);					break;		/* BIT	*/
		case 0x84:	ProgramZPG(i);		ProgramSTY(i);					break;		/* STY	*/
		case 0x94:	ProgramZPX(i);		ProgramSTY(i);					break;		/* STY	*/
		case 0xa4:	ProgramZPG(i);		ProgramLDY(i);					break;		/* LDY	*/
		case 0xb4:	ProgramZPX(i);		ProgramLDY(i);					break;		/* LDY	*/
		case 0xc4:	ProgramZPG(i);		ProgramCPY(i);					break;		/* CPY	*/
		case 0xe4:	ProgramZPG(i);		ProgramCPX(i);					break;		/* CPX	*/

		case 0x05:	ProgramZPG(i);		ProgramORA(i);					break;		/* ORA	*/
		case 0x15:	ProgramZPX(i);		ProgramORA(i);					break;		/* ORA	*/
		case 0x25:	ProgramZPG(i);		ProgramAND(i);					break;		/* AND	*/
		case 0x35:	ProgramZPX(i);		ProgramAND(i);					break;		/* AND	*/
		case 0x45:	ProgramZPG(i);		ProgramEOR(i);					break;		/* EOR	*/
		case 0x55:	ProgramZPX(i);		ProgramEOR(i);					break;		/* EOR	*/
		case 0x65:	ProgramZPG(i);		ProgramADC(i);					break;		/* ADC	*/
		case 0x75:	ProgramZPX(i);		ProgramADC(i);					break;		/* ADC	*/
		case 0x85:	ProgramZPG(i);		ProgramSTA(i);					break;		/* STA	*/
		case 0x95:	ProgramZPX(i);		ProgramSTA(i);					break;		/* STA	*/
		case 0xa5:	ProgramZPG(i);		ProgramLDA(i);					break;		/* LDA	*/
		case 0xb5:	ProgramZPX(i);		ProgramLDA(i);					break;		/* LDA	*/
		case 0xc5:	ProgramZPG(i);		ProgramCMP(i);					break;		/* CMP	*/
		case 0xd5:	ProgramZPX(i);		ProgramCMP(i);					break;		/* CMP	*/
		case 0xe5:	ProgramZPG(i);		ProgramSBC(i);					break;		/* SBC	*/
		case 0xf5:	ProgramZPX(i);		ProgramSBC(i);					break;		/* SBC	*/

		case 0x06:	ProgramZPG(i);		ProgramASL(i);					break;		/* ASL	*/
		case 0x16:	ProgramZPX(i);		ProgramASL(i);					break;		/* ASL	*/
		case 0x26:	ProgramZPG(i);		ProgramROL(i);					break;		/* ROL	*/
		case 0x36:	ProgramZPX(i);		ProgramROL(i);					break;		/* ROL	*/
		case 0x46:	ProgramZPG(i);		ProgramLSR(i);					break;		/* LSR	*/
		case 0x56:	ProgramZPX(i);		ProgramLSR(i);					break;		/* LSR	*/
		case 0x66:	ProgramZPG(i);		ProgramROR(i);					break;		/* ROR	*/
		case 0x76:	ProgramZPX(i);		ProgramROR(i);					break;		/* ROR	*/
		case 0x86:	ProgramZPG(i);		ProgramSTX(i);					break;		/* STX	*/
		case 0x96:	ProgramZPY(i);		ProgramSTX(i);					break;		/* STX	*/
		case 0xa6:	ProgramZPG(i);		ProgramLDX(i);					break;		/* LDX	*/
		case 0xb6:	ProgramZPY(i);		ProgramLDX(i);					break;		/* LDX	*/
		case 0xc6:	ProgramZPG(i);		ProgramDEC(i);					break;		/* DEC	*/
		case 0xd6:	ProgramZPX(i);		ProgramDEC(i);					break;		/* DEC	*/
		case 0xe6:	ProgramZPG(i);		ProgramINC(i);					break;		/* INC	*/
		case 0xf6:	ProgramZPX(i);		ProgramINC(i);					break;		/* INC	*/

		case 0x08:						ProgramPHP(i);					break;		/* PHP	*/
		case 0x18:						ProgramFLAGOP(i);				break;		/* CLC	*/
		case 0x28:						ProgramPLP(i);					break;		/* PLP	*/
		case 0x38:						ProgramFLAGOP(i);				break;		/* SEC	*/
		case 0x48:						ProgramPHA(i);					break;		/* PHA	*/
		case 0x58:						ProgramFLAGOP(i);				break;		/* CLI	*/
		case 0x68:						ProgramPLA(i);					break;		/* PLA	*/
		case 0x78:						ProgramFLAGOP(i);				break;		/* SEI	*/
		case 0x88:						ProgramDEY(i);					break;		/* DEY	*/
		case 0x98:						ProgramTYA(i);					break;		/* TYA	*/
		case 0xa8:						ProgramTAY(i);					break;		/* TAY	*/
		case 0xb8:						ProgramFLAGOP(i);				break;		/* CLV	*/
		case 0xc8:						ProgramINY(i);					break;		/* INY	*/
		case 0xd8:						ProgramFLAGOP(i);				break;		/* CLD	*/
		case 0xe8:						ProgramINX(i);					break;		/* INX	*/
		case 0xf8:						ProgramFLAGOP(i);				break;		/* SED	*/

		case 0x09:	ProgramIMM(i);		ProgramORA(i);					break;		/* ORA	*/
		case 0x19:	ProgramABY(i);		ProgramORA(i);					break;		/* ORA	*/
		case 0x29:	ProgramIMM(i);		ProgramAND(i);					break;		/* AND	*/
		case 0x39:	ProgramABY(i);		ProgramAND(i);					break;		/* AND	*/
		case 0x49:	ProgramIMM(i);		ProgramEOR(i);					break;		/* EOR	*/
		case 0x59:	ProgramABY(i);		ProgramEOR(i);					break;		/* EOR	*/
		case 0x69:	ProgramIMM(i);		ProgramADC(i);					break;		/* ADC	*/
		case 0x79:	ProgramABY(i);		ProgramADC(i);					break;		/* ADC	*/
		case 0x99:	ProgramABY(i);		ProgramSTA(i);					break;		/* STA	*/
		case 0xa9:	ProgramIMM(i);		ProgramLDA(i);					break;		/* LDA	*/
		case 0xb9:	ProgramABY(i);		ProgramLDA(i);					break;		/* LDA	*/
		case 0xc9:	ProgramIMM(i);		ProgramCMP(i);					break;		/* CMP	*/
		case 0xd9:	ProgramABY(i);		ProgramCMP(i);					break;		/* CMP	*/
		case 0xe9:	ProgramIMM(i);		ProgramSBC(i);					break;		/* SBC	*/
		case 0xf9:	ProgramABY(i);		ProgramSBC(i);					break;		/* SBC	*/

		case 0x0a:						ProgramASLA(i);					break;		/* ASLA	*/
		case 0x2a:						ProgramROLA(i);					break;		/* ROLA	*/
		case 0x4a:						ProgramLSRA(i);					break;		/* LSRA	*/
		case 0x6a:						ProgramRORA(i);					break;		/* RORA	*/
		case 0x8a:						ProgramTXA(i);					break;		/* TXA	*/
		case 0x9a:						ProgramTXS(i);					break;		/* TXS	*/
		case 0xaa:						ProgramTAX(i);					break;		/* TAX	*/
		case 0xba:						ProgramTSX(i);					break;		/* TSX	*/
		case 0xca:						ProgramDEX(i);					break;		/* DEX	*/
		case 0xea:						ProgramNOP(i);					break;		/* NOP	*/

		case 0x2c:	ProgramABS(i);		ProgramBIT(i);					break;		/* BIT 	*/
		case 0x4c:						ProgramJMP(i);					break;		/* JMP 	*/
		case 0x6c:						ProgramJMPI(i);					break;		/* JMP	*/
		case 0x8c:	ProgramABS(i);		ProgramSTY(i);					break;		/* STY	*/
		case 0xac:	ProgramABS(i);		ProgramLDY(i);					break;		/* LDY	*/
		case 0xbc:	ProgramABX(i);		ProgramLDY(i);					break;		/* LDY	*/
		case 0xcc:	ProgramABS(i);		ProgramCPY(i);					break;		/* CPY	*/
		case 0xec:	ProgramABS(i);		ProgramCPX(i);					break;		/* CPX	*/

		case 0x0d:	ProgramABS(i);		ProgramORA(i);					break;		/* ORA	*/
		case 0x1d:	ProgramABX(i);		ProgramORA(i);					break;		/* ORA	*/
		case 0x2d:	ProgramABS(i);		ProgramAND(i);					break;		/* AND	*/
		case 0x3d:	ProgramABX(i);		ProgramAND(i);					break;		/* AND	*/
		case 0x4d:	ProgramABS(i);		ProgramEOR(i);					break;		/* EOR	*/
		case 0x5d:	ProgramABX(i);		ProgramEOR(i);					break;		/* EOR	*/
		case 0x6d:	ProgramABS(i);		ProgramADC(i);					break;		/* ADC	*/
		case 0x7d:	ProgramABX(i);		ProgramADC(i);					break;		/* ADC	*/
		case 0x8d:	ProgramABS(i);		ProgramSTA(i);					break;		/* STA	*/
		case 0x9d:	ProgramABX(i);		ProgramSTA(i);					break;		/* STA	*/
		case 0xad:	ProgramABS(i);		ProgramLDA(i);					break;		/* LDA	*/
		case 0xbd:	ProgramABX(i);		ProgramLDA(i);					break;		/* LDA	*/
		case 0xcd:	ProgramABS(i);		ProgramCMP(i);					break;		/* CMP	*/
		case 0xdd:	ProgramABX(i);		ProgramCMP(i);					break;		/* CMP	*/
		case 0xed:	ProgramABS(i);		ProgramSBC(i);					break;		/* SBC	*/
		case 0xfd:	ProgramABX(i);		ProgramSBC(i);					break;		/* SBC	*/

		case 0x0e:	ProgramABS(i);		ProgramASL(i);					break;		/* ASL	*/
		case 0x1e:	ProgramABX(i);		ProgramASL(i);					break;		/* ASL	*/
		case 0x2e:	ProgramABS(i);		ProgramROL(i);					break;		/* ROL	*/
		case 0x3e:	ProgramABX(i);		ProgramROL(i);					break;		/* ROL	*/
		case 0x4e:	ProgramABS(i);		ProgramLSR(i);					break;		/* LSR	*/
		case 0x5e:	ProgramABX(i);		ProgramLSR(i);					break;		/* LSR	*/
		case 0x6e:	ProgramABS(i);		ProgramROR(i);					break;		/* ROR	*/
		case 0x7e:	ProgramABX(i);		ProgramROR(i);					break;		/* ROR	*/
		case 0x8e:	ProgramABS(i);		ProgramSTX(i);					break;		/* STX	*/
		case 0xae:	ProgramABS(i);		ProgramLDX(i);					break;		/* LDX	*/
		case 0xbe:	ProgramABY(i);		ProgramLDX(i);					break;		/* LDX	*/
		case 0xce:	ProgramABS(i);		ProgramDEC(i);					break;		/* DEC	*/
		case 0xde:	ProgramABX(i);		ProgramDEC(i);					break;		/* DEC	*/
		case 0xee:	ProgramABS(i);		ProgramINC(i);					break;		/* INC	*/
		case 0xfe:	ProgramABX(i);		ProgramINC(i);					break;		/* INC	*/
		default:					    ProgramNOP(i);					break;		/* NOP	*/
			break; 
		}

	}
	ProgramRESET ();
	WriteEPROM();


	return 0;
}

unsigned char areg, breg, eal, eah, ebl, ebh;
unsigned char g_SAPRegisters[16];
unsigned char updateNZ[256] = {
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

int uflag = 0;

unsigned char ReadRegister(unsigned long long controlWire)
{
	unsigned int result = 0, t1, t2 = 0, tl;
	int reg = (controlWire >> DRIVER) & 0x0f;
	unsigned int carryin = (controlWire & CARRYZERO) ? 0 : g_SAPRegisters[STREG] & 0x01;
	if (controlWire & CARRYONE) carryin = 1;
	if (reg == 0) {		//	ALU operation
		g_SAPRegisters[STREG] &= (~((1 << PFLAG) | (1 << UFLAG)));
		switch ((controlWire >> ALUOP) & 0x1f) {
		case ALUORA:	//	ORA
			result = g_SAPRegisters[AH] | g_SAPRegisters[BREG];
			if (controlWire & UPDATENZ) g_SAPRegisters[STREG] = (g_SAPRegisters[STREG] & 0x7d) + updateNZ[result];
			break;
		case ALUAND:	//	AND
			result = g_SAPRegisters[AH] & g_SAPRegisters[BREG];
			if (controlWire & UPDATENZ) g_SAPRegisters[STREG] = (g_SAPRegisters[STREG] & 0x7d) | updateNZ[result];
			if (controlWire & BITOP) {
				if (controlWire & UPDATENZ) {
					g_SAPRegisters[STREG] = (g_SAPRegisters[STREG] & 0x7f) | (g_SAPRegisters[BREG] & 0x80);
				}
				if (controlWire & UPDATEV) {
					g_SAPRegisters[STREG] = (g_SAPRegisters[STREG] & 0xbf) | (g_SAPRegisters[BREG] & 0x40);
				}
			}
			break;
		case ALUXOR:	//	EOR
			result = g_SAPRegisters[AH] ^ g_SAPRegisters[BREG];
			if (controlWire & UPDATENZ) g_SAPRegisters[STREG] = (g_SAPRegisters[STREG] & 0x7d) + updateNZ[result];
			break;
		case ALUADC:
			if ((g_SAPRegisters[STREG] & 0x08) && (!(controlWire & NOBCD))) {
				tl = (g_SAPRegisters[AH] & 0x0f) + (g_SAPRegisters[BREG] & 0x0f) + (carryin);
				if (tl > 9) tl += 6;
				tl = tl + (g_SAPRegisters[AH] & 0xf0) + (g_SAPRegisters[BREG] & 0xf0);
				if (controlWire & UPDATENZ) {
					g_SAPRegisters[STREG] = (g_SAPRegisters[STREG] & 0xfd) + (updateNZ[(g_SAPRegisters[AH] + g_SAPRegisters[BREG] + (carryin)) & 0xff] & 0x02);
					g_SAPRegisters[STREG] = (g_SAPRegisters[STREG] & 0x7f) + (updateNZ[tl & 0xff] & 0x80);
				}
				if (controlWire & UPDATEV) {
					if (controlWire & SBC)  g_SAPRegisters[STREG] = (g_SAPRegisters[STREG] & 0xbf) + ((((g_SAPRegisters[AH] & 0x80) == (g_SAPRegisters[BREG] & 0x80)) && ((g_SAPRegisters[AH] & 0x80) != (t2 & 0x80))) ? 0x40 : 0x00);
					else 					g_SAPRegisters[STREG] = (g_SAPRegisters[STREG] & 0xbf) + ((((g_SAPRegisters[AH] & 0x80) == (g_SAPRegisters[BREG] & 0x80)) && ((g_SAPRegisters[AH] & 0x80) != (tl & 0x80))) ? 0x40 : 0x00);

				}
				if ((tl & 0x1f0) > 0x90) tl += 0x60;
				if (controlWire & UPDATEC) g_SAPRegisters[STREG] = (g_SAPRegisters[STREG] & 0xfe) + ((tl >> 8) & 0x01);
				result = tl & 0xff;
			}
			else {
				tl = g_SAPRegisters[AH] + g_SAPRegisters[BREG] + carryin;
				if (controlWire & UPDATEC) g_SAPRegisters[STREG] = (g_SAPRegisters[STREG] & 0xfe) + ((tl & 0x100) ? 0x01 : 0x00);
				g_SAPRegisters[STREG] |= ((tl & 0x100) ? (1 << PFLAG) : 0x00);
				if (controlWire & UPDATEV) {
					if (controlWire & SBC)  g_SAPRegisters[STREG] = (g_SAPRegisters[STREG] & 0xbf) + ((((g_SAPRegisters[AH] & 0x80) == (g_SAPRegisters[BREG] & 0x80)) && ((g_SAPRegisters[AH] & 0x80) != (tl & 0x80))) ? 0x40 : 0x00);
					else				    g_SAPRegisters[STREG] = (g_SAPRegisters[STREG] & 0xbf) + ((((g_SAPRegisters[AH] & 0x80) == (g_SAPRegisters[BREG] & 0x80)) && ((g_SAPRegisters[AH] & 0x80) != (tl & 0x80))) ? 0x40 : 0x00);
				}
				result = tl & 0xff;
				if (controlWire & UPDATENZ) g_SAPRegisters[STREG] = (g_SAPRegisters[STREG] & 0x7d) + updateNZ[result];
			}
			//	Special Check for branch instructions crossing pages, and if so, which direction
			break;
		case ALUBREG:	//	LD
			result = g_SAPRegisters[BREG];
			if (controlWire & SHIFTRIGHT) {
				g_SAPRegisters[STREG] = (g_SAPRegisters[STREG] & 0xfe) + ((result & 0x01) ? 0x01 : 0x00);
				result = (result >> 1) | (carryin ? 0x80 : 0x00);
			}
			if (controlWire & UPDATENZ) g_SAPRegisters[STREG] = (g_SAPRegisters[STREG] & 0x7d) + updateNZ[result];
			uflag = (g_SAPRegisters[BREG] & 0x80) ? 1 : 0;
			break;

		case ALUSBC:			//	SBC	
			g_SAPRegisters[BREG] = g_SAPRegisters[BREG]^0xff;
			if ((g_SAPRegisters[STREG] & 0x08) && (!(controlWire & NOBCD))) {
				t2 = g_SAPRegisters[AH] + g_SAPRegisters[BREG] + g_SAPRegisters[STREG] & 0x01;
				g_SAPRegisters[BREG] ^= 0xff;
				tl = (g_SAPRegisters[AH] & 0x0f) - (g_SAPRegisters[BREG] & 0x0f) - (!carryin);
				if ((tl & 0x10)) {
					tl = ((tl - 6) & 0x0f) | ((g_SAPRegisters[AH] & 0xf0) - (g_SAPRegisters[BREG] & 0xf0) - 0x10);
				}
				else {
					tl = (tl & 0x0f) | ((g_SAPRegisters[AH] & 0xf0) - (g_SAPRegisters[BREG] & 0xf0));
				}
				if (tl & 0x100) {
					tl -= 0x60;
				}
				if (controlWire & UPDATENZ) {
					g_SAPRegisters[STREG] = (g_SAPRegisters[STREG] & 0xfd) + (updateNZ[t2 & 0xff] & 0x02);
					g_SAPRegisters[STREG] = (g_SAPRegisters[STREG] & 0x7f) + (updateNZ[t2 & 0xff] & 0x80);
				}
				if (controlWire & UPDATEV) {
					if (controlWire & SBC) g_SAPRegisters[STREG] = (g_SAPRegisters[STREG] & 0xbf) + ((((g_SAPRegisters[AH] & 0x80) == (g_SAPRegisters[BREG] & 0x80)) && ((g_SAPRegisters[AH] & 0x80) != (t2 & 0x80))) ? 0x40 : 0x00);
				}
				if (controlWire & UPDATEC)	g_SAPRegisters[STREG] = (g_SAPRegisters[STREG] & 0xfe) + ((t2 < 0x100) & 0x01);

				result = tl & 0xff;
			}
			else {
				tl = g_SAPRegisters[AH] + g_SAPRegisters[BREG] + (carryin);
				if (controlWire & UPDATEC) g_SAPRegisters[STREG] = (g_SAPRegisters[STREG] & 0xfe) + ((tl & 0x100) ? 0x01 : 0x00);
				if (controlWire & UPDATEV) {
					if (controlWire & SBC)  g_SAPRegisters[STREG] = (g_SAPRegisters[STREG] & 0xbf) + ((((g_SAPRegisters[AH] & 0x80) == (g_SAPRegisters[BREG] & 0x80)) && ((g_SAPRegisters[AH] & 0x80) != (tl & 0x80))) ? 0x40 : 0x00);
				}
				result = tl & 0xff;

				if (controlWire & UPDATENZ) g_SAPRegisters[STREG] = (g_SAPRegisters[STREG] & 0x7d) + updateNZ[result];
			}
			break;
		}
	}
	else {
		result = g_SAPRegisters[reg];
		if (reg == STREG) result |= 0x30;
	}
	return result;
}

void WriteRegister(int reg, unsigned int wbus)
{
	g_SAPRegisters[reg & 0x0f] = wbus;
}


int UseTuring(int ir)
{ 

	switch (ir) {
//	case 0x00: return 7;
	case 0x00: return 0;
	case 0x01: return 6;
	case 0x02: return 2;	// invalid
	case 0x03: return 8;	// invalid
	case 0x04: return 3;	// invalid
	case 0x05: return 3;
	case 0x06: return 5;
	case 0x07: return 5;	// invalid 
	case 0x08: return 3;
	case 0x09: return 2;
	case 0x0A: return 2;
	case 0x0B: return 2;	// invalid
	case 0x0C: return 4;	// invalid
	case 0x0D: return 4;
	case 0x0E: return 6;
	case 0x0F: return 6;	// invalid
	case 0x10: return 2;
 	case 0x11: return 5;
	case 0x12: return 2;	// invalid
	case 0x13: return 8;	// invalid
	case 0x14: return 4;	// invalid
	case 0x15: return 4;
	case 0x16: return 6;
	case 0x17: return 6;	// invalid
	case 0x18: return 2;
	case 0x19: return 4;
	case 0x1A: return 2;	// invalid
	case 0x1B: return 7;	// invalid
	case 0x1C: return 4;	// invalid
	case 0x1D: return 4;
	case 0x1E: return 7;
	case 0x1F: return 7;	// invalid
	case 0x20: return 6;
	case 0x21: return 6;
	case 0x22: return 2;	// invalid
	case 0x23: return 8;	// invalid
	case 0x24: return 3;
	case 0x25: return 3;
	case 0x26: return 5;
	case 0x27: return 5;	// invalid
	case 0x28: return 4;
	case 0x29: return 2;
	case 0x2A: return 2;
	case 0x2B: return 2;	// invalid
	case 0x2C: return 4;
	case 0x2D: return 4;
	case 0x2E: return 6;
	case 0x2F: return 6;	// invalid
	case 0x30: return 2;
	case 0x31: return 5;
	case 0x32: return 2;	// invalid
	case 0x33: return 8;	// invalid
	case 0x34: return 4;	// invalid
	case 0x35: return 4;
	case 0x36: return 6;
	case 0x37: return 6;	// invalid
	case 0x38: return 2;
	case 0x39: return 4;
	case 0x3A: return 2;	// invalid
	case 0x3B: return 7;	// invalid
	case 0x3C: return 4;	// invalid
	case 0x3D: return 4;
	case 0x3E: return 7;
	case 0x3F: return 7;	// invalid
//	case 0x40: return 6;
	case 0x40: return 0;
	case 0x41: return 6;
	case 0x42: return 2;	// invalid
	case 0x43: return 8;	// invalid
	case 0x44: return 3;	// invalid
	case 0x45: return 3;
	case 0x46: return 5;
	case 0x47: return 5;	// invalid
	case 0x48: return 3;
	case 0x49: return 2;
	case 0x4A: return 2;
	case 0x4B: return 2;	// invalid
	case 0x4C: return 3;
	case 0x4D: return 4;
	case 0x4E: return 6;
	case 0x4F: return 6;	// invalid
	case 0x50: return 2;
	case 0x51: return 5;
	case 0x52: return 2;	// invalid
	case 0x53: return 8;	// invalid
	case 0x54: return 4;	// invalid
	case 0x55: return 4;
	case 0x56: return 6;
	case 0x57: return 6;	// invalid
	case 0x58: return 2;
	case 0x59: return 4;
	case 0x5A: return 2;	// invalid
	case 0x5B: return 7;	// invalid
	case 0x5C: return 4;	// invalid
	case 0x5D: return 4;
	case 0x5E: return 7;
	case 0x5F: return 7;	// invalid
	case 0x60: return 6;
	case 0x61: return 6;
	case 0x62: return 2;	// invalid
	case 0x63: return 8;	// invalid
	case 0x64: return 3;	// invalid
	case 0x65: return 3;
	case 0x66: return 5;
	case 0x67: return 5;	// invalid
	case 0x68: return 4;
	case 0x69: return 2;
	case 0x6A: return 2;
	case 0x6B: return 2;	// invalid
	case 0x6C: return 5; // GH#264
	case 0x6D: return 4;
	case 0x6E: return 6;
	case 0x6F: return 6;	// invalid
	case 0x70: return 2;
	case 0x71: return 5;
	case 0x72: return 2;	// invalid
	case 0x73: return 8;	// invalid
	case 0x74: return 4;	// invalid
	case 0x75: return 4;
	case 0x76: return 6;
	case 0x77: return 6;	// invalid
	case 0x78: return 2;
	case 0x79: return 4;
	case 0x7A: return 2;	// invalid
	case 0x7B: return 7;	// invalid
	case 0x7C: return 4;	// invalid
	case 0x7D: return 4;
	case 0x7E: return 7;
	case 0x7F: return 7;	// invalid
	case 0x80: return 2;	// invalid
	case 0x81: return 6;
	case 0x82: return 2;	// invalid
	case 0x83: return 6;	// invalid
	case 0x84: return 3;
	case 0x85: return 3;
	case 0x86: return 3;
	case 0x87: return 3;	// invalid
	case 0x88: return 2;
	case 0x89: return 2;	// invalid
	case 0x8A: return 2;
	case 0x8B: return 2;	// invalid
	case 0x8C: return 4;
	case 0x8D: return 4;
	case 0x8E: return 4;
	case 0x8F: return 4;	// invalid
	case 0x90: return 2;
	case 0x91: return 6;
	case 0x92: return 2;	// invalid
	case 0x93: return 6;	// invalid
	case 0x94: return 4;
	case 0x95: return 4;
	case 0x96: return 4;
	case 0x97: return 4;	// invalid
	case 0x98: return 2;
	case 0x99: return 5;
	case 0x9A: return 2;
	case 0x9B: return 5;	// invalid
	case 0x9C: return 5;	// invalid
	case 0x9D: return 5;
	case 0x9E: return 5;	// invalid
	case 0x9F: return 5;	// invalid
	case 0xA0: return 2;
	case 0xA1: return 6;
	case 0xA2: return 2;
	case 0xA3: return 6;	// invalid
	case 0xA4: return 3;
	case 0xA5: return 3;
	case 0xA6: return 3;
	case 0xA7: return 3;	// invalid
	case 0xA8: return 2;
	case 0xA9: return 2;
	case 0xAA: return 2;
	case 0xAB: return 2;	// invalid
	case 0xAC: return 4;
	case 0xAD: return 4;
	case 0xAE: return 4;
	case 0xAF: return 4;	// invalid
	case 0xB0: return 2;
	case 0xB1: return 5;
	case 0xB2: return 2;	// invalid
	case 0xB3: return 5;	// invalid
	case 0xB4: return 4;
	case 0xB5: return 4;
	case 0xB6: return 4;
	case 0xB7: return 4;	// invalid
	case 0xB8: return 2;
	case 0xB9: return 4;
	case 0xBA: return 2;
	case 0xBB: return 4;	// invalid
	case 0xBC: return 4;
	case 0xBD: return 4;
	case 0xBE: return 4;
	case 0xBF: return 4;	// invalid
	case 0xC0: return 2;
	case 0xC1: return 6;
	case 0xC2: return 2;	// invalid
	case 0xC3: return 8;	// invalid
	case 0xC4: return 3;
	case 0xC5: return 3;
	case 0xC6: return 5;
	case 0xC7: return 5;	// invalid
	case 0xC8: return 2;
	case 0xC9: return 2;
	case 0xCA: return 2;
	case 0xCB: return 2;	// invalid
	case 0xCC: return 4;
	case 0xCD: return 4;
	case 0xCE: return 6;
	case 0xCF: return 6;	// invalid
	case 0xD0: return 2;
	case 0xD1: return 5;
	case 0xD2: return 2;	// invalid
	case 0xD3: return 8;	// invalid
	case 0xD4: return 4;	// invalid
	case 0xD5: return 4;
	case 0xD6: return 6;
	case 0xD7: return 6;	// invalid
	case 0xD8: return 2;
	case 0xD9: return 4;
	case 0xDA: return 2;	// invalid
	case 0xDB: return 7;	// invalid
	case 0xDC: return 4;	// invalid
	case 0xDD: return 4;
	case 0xDE: return 7;
	case 0xDF: return 7;	// invalid
	case 0xE0: return 2;
	case 0xE1: return 6;
	case 0xE2: return 2;	// invalid
	case 0xE3: return 8;	// invalid
	case 0xE4: return 3;
	case 0xE5: return 3;
	case 0xE6: return 5;
	case 0xE7: return 5;	// invalid
	case 0xE8: return 2;
	case 0xE9: return 2;
	case 0xEA: return 2;
	case 0xEB: return 2;	// invalid
	case 0xEC: return 4;
	case 0xED: return 4;
	case 0xEE: return 6;
	case 0xEF: return 6;	// invalid
	case 0xF0: return 2;
	case 0xF1: return 5;
	case 0xF2: return 2;	// invalid
	case 0xF3: return 8;	// invalid
	case 0xF4: return 4;	// invalid
	case 0xF5: return 4;
	case 0xF6: return 6;
	case 0xF7: return 6;	// invalid 
	case 0xF8: return 2;
	case 0xF9: return 4;
	case 0xFA: return 2;	// invalid
	case 0xFB: return 7;	// invalid
	case 0xFC: return 4;	// invalid
	case 0xFD: return 4;
	case 0xFE: return 7;
	case 0xFF: return 7;	// invalid 
	}
	return 0;
}

unsigned char ReadMemory(int address)
{
	return *(mem + address);
}

int read_error = 0;
int	ExecuteSAP6502(ULONG uExecutedCycles)
{
	long long controlWires;
	unsigned char ir = *(mem + regs.pc);
	unsigned char wbus;
	unsigned char uCount = 1;
	int cycles = 0;;
	controlWires = g_controlROM[0];

	if (cycles = UseTuring(ir)) {

		g_SAPRegisters[STREG] = regs.ps;
		g_SAPRegisters[AREG] = regs.a;
		g_SAPRegisters[PCL] = (regs.pc) & 0x0ff;
		g_SAPRegisters[PCH] = (regs.pc >> 8) & 0x0ff;
		g_SAPRegisters[XREG] = regs.x;
		g_SAPRegisters[YREG] = regs.y;
		g_SAPRegisters[SPREG] = (regs.sp & 0xff);
		g_SAPRegisters[IREG] = ir;

		controlWires = g_controlROM[256 + ir];
		g_SAPRegisters[PCL] += 1;	if (g_SAPRegisters[PCL] < 1) g_SAPRegisters[PCH]++;
		
		do {
			//	Clock is low
			unsigned int address = 0x00;
			if (controlWires & PCSEL) address = ((g_SAPRegisters[PCH] << 8) + g_SAPRegisters[PCL]);
			else address = ((g_SAPRegisters[EAH] << 8) + g_SAPRegisters[EAL]);
			unsigned int addr = address;
			//	perform a memory read

			if ((controlWires & MEMACCESS) && (!(controlWires & MWRITE))) {
				wbus = READ;				
			}
			else {
				wbus = ReadRegister(controlWires); 
			}
			if (controlWires & IREGLOAD) g_SAPRegisters[IREG] = wbus;

			//	Clock low-to-high transition
			if (controlWires & FLAGINST) {
				switch (g_SAPRegisters[IREG]) {
				case 0x18:	g_SAPRegisters[STREG] &= 0xfe;		break;		//		CLC
				case 0x38:	g_SAPRegisters[STREG] |= 0x01;		break;		//		SEC
				case 0x58:	g_SAPRegisters[STREG] &= 0xfd;		break;		//		CLI
				case 0x78:	g_SAPRegisters[STREG] |= 0x04;		break;		//		SEI
				case 0xb8:	g_SAPRegisters[STREG] &= 0xdf;		break;		//		CLV
				case 0xd8:	g_SAPRegisters[STREG] &= 0xf7;		break;		//		CLD
				case 0xf8:	g_SAPRegisters[STREG] |= 0x08;		break;		//		SED
				}
			}

			//  Clock high
			if ((controlWires & MEMACCESS) && (controlWires & MWRITE)) {
				//				AppleRAM [address] = wbus;
				WRITE(wbus);
			}
			else WriteRegister((controlWires >> LOAD) & 0x0f, wbus);


			//	Clock high-to-low transition
			if ((controlWires & PCCLOCKLO) && (controlWires & PCCLOCKHI)) {
				if (g_SAPRegisters[PCL] == 0xff) {
					g_SAPRegisters[PCL] = 0;
					g_SAPRegisters[PCH] = (g_SAPRegisters[PCH] + 1) & 0xff;
				}
				else g_SAPRegisters[PCL]++;
			}

			uCount = (uCount + 1) & 0x1f;
			if (controlWires & UCOUNTERRESET) uCount = 0;
			unsigned int controlAddress = g_SAPRegisters[IREG] + (uCount << 8);
			if (((controlWires >> FLAGSELECT) & 7) != UFLAG) controlAddress |= (g_SAPRegisters[STREG] & (1 << ((controlWires >> FLAGSELECT) & 7))) ? FLAGBIT : 0;
			else controlAddress |= (uflag) ? FLAGBIT : 0;
			controlWires = g_controlROM[controlAddress];
			g_SAPRegisters[CONSTR] = ((controlWires >> CONSTRANT) & 0x0f);
			if (g_SAPRegisters[CONSTR] & 0x08) g_SAPRegisters[CONSTR] |= 0xf0;

		} while (uCount != 0);


		regs.ps = g_SAPRegisters[STREG];
		regs.a = g_SAPRegisters[AREG];
		regs.pc = (g_SAPRegisters[PCH] << 8) + g_SAPRegisters[PCL];
		regs.x = g_SAPRegisters[XREG];
		regs.y = g_SAPRegisters[YREG];
		regs.sp = g_SAPRegisters[SPREG]+0x100;

	}
	return cycles;
}


//===========================================================================


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

#undef READ
#undef WRITE
#undef HEATMAP_X

//===========================================================================

static DWORD InternalCpuExecute(const DWORD uTotalCycles, const bool bVideoUpdate)
{
	
	ProgramControlROM();
	if (g_nAppMode == MODE_RUNNING || g_nAppMode == MODE_BENCHMARK)
	{
		if (GetMainCpu() == CPU_6502) {
			ULONG uExecutedCycles = 0;
			ULONG uCurrentCycles = 0;
			do {
				uCurrentCycles = ExecuteSAP6502(uExecutedCycles);
				if (!uCurrentCycles) {
					uCurrentCycles = Cpu6502(uExecutedCycles, false);   // Apple ][, ][+, //e, Clones
				}
				uExecutedCycles += uCurrentCycles;
				CheckSynchronousInterruptSources(uCurrentCycles, uExecutedCycles);
				// NTSC_BEGIN
				if (bVideoUpdate)
				{
					NTSC_VideoUpdateCycles(uCurrentCycles);
				}
				// NTSC_END
			} while (uExecutedCycles < uTotalCycles);
			return uExecutedCycles;		// Apple ][, ][+, //e, Clones
		}
		else
			return Cpu65C02(uTotalCycles, bVideoUpdate);	// Enhanced Apple //e
	}
	else
	{
		_ASSERT(g_nAppMode == MODE_STEPPING || g_nAppMode == MODE_DEBUG);
		if (GetMainCpu() == CPU_6502)
			return Cpu6502_debug(uTotalCycles, bVideoUpdate);	// Apple ][, ][+, //e, Clones
		else
			return Cpu65C02_debug(uTotalCycles, bVideoUpdate);	// Enhanced Apple //e
	}
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
	

	_ASSERT((LONG)nCycles >= 0);
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
