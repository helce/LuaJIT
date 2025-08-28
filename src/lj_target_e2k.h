/*
** Definitions for E2K CPUs.
** Copyright (C) 2005-2021 Mike Pall. See Copyright Notice in luajit.h
*/

#ifndef _LJ_TARGET_E2K_H
#define _LJ_TARGET_E2K_H

/* -- Registers IDs ------------------------------------------------------- */

/* Use registers from pipeline state to avoid misscomunications */
/* r0-r15 - direct, b0-b35 - rotating, r52-r59 - scratch(arguments) */
/* g16-g31 - global, pred1-pred3 - predicates, ctpr1-ctpr3 - cf */

#define GPRDEF(_) \
   _(R0)  _(R1)  _(R2)  _(R3)  _(R4)  _(R5)  _(R6)  _(R7) \
   _(R8)  _(R9) _(R10) _(R11) _(R12) _(R13) _(R14) _(R15) \
  _(R52) _(R53) _(R54) _(R55) _(R56) _(R57) _(R58) _(R59)

#define FPRDEF(_)

#define BREGDEF(_) \
   _(B0)  _(B1) _(B2)  _(B3)  _(B4)  _(B5)  _(B6)  _(B7) _(B8)  _(B9) \
  _(B10) _(B11) _(B12) _(B13) _(B14) _(B15)

#define GREGDEF(_) \
  _(G16) _(G17) _(G18) _(G19)

#define PREDREGDEF(_) \
   _(PRED0)  _(PRED1)  _(PRED2)  _(PRED3)

#define CTPRDEF(_) \
  _(CTPR1) _(CTPR2) _(CTPR3)

#define VRIDDEF(_)

#define RIDENUM(name) RID_##name,

enum {
  GPRDEF(RIDENUM)  /* Directly addressable registers of the current window */
  BREGDEF(RIDENUM)  /* Rotating registers of the current window */
  GREGDEF(RIDENUM)  /* Global registers */
  PREDREGDEF(RIDENUM) /* Predicates */
  CTPRDEF(RIDENUM) /* Control transer preparation registers */
  RID_MAX,
  RID_TMP  = RID_G16,
  RID_TMP1 = RID_G16,
  RID_TMP2 = RID_G17,
  RID_TMP3 = RID_G18,
  RID_TMP4 = RID_G19,
  RID_BASE = RID_R4,  /* Interpreter BASE */
  RID_SP = RID_R6,  /* Interpreter stack pointer */
  RID_LPC = RID_R7, /* Interpreter PC */
  RID_DISPATCH = RID_R8, /* Interpreter dispatch */
  /* Calling conventions */
  RID_RETLO = RID_R52,
  RID_RETHI = RID_R53,
  RID_RET = RID_R52,
  RID_FPRET = RID_R52,

  RID_MIN_GPR = RID_R0,
  RID_MAX_GPR = RID_CTPR3+1,
  RID_MIN_FPR = 0,
  RID_MAX_FPR = RID_MIN_FPR,

  RID_NUM_R   = RID_B15 + 1 - RID_R0,
  RID_NUM_GPR = RID_MAX_GPR - RID_MIN_GPR,
  RID_NUM_FPR = RID_MAX_FPR - RID_MIN_FPR
};

#define RID_NUM_KREF		RID_NUM_R
#define RID_MIN_KREF		RID_R0

/* -- Register sets ------------------------------------------------------- */

/* Make use of all registers, except SP */
#define RSET_FIXED \
    (RID2RSET(RID_SP)|RID2RSET(RID_DISPATCH))
#define RSET_GPR    (RSET_RANGE(RID_R0, RID_B15+1) - RSET_FIXED)
#define RSET_PRED   (RSET_RANGE(RID_PRED0, RID_PRED3+1))
#define RSET_CTPR   (RSET_RANGE(RID_CTPR1, RID_CTPR3+1))
#define RSET_FPR    0
#define RSET_ALL    (RSET_GPR|RSET_PRED|RSET_CTPR)
#define RSET_INIT   RSET_ALL

/* In pipe state scratch registers are r52-r59 */
#define RSET_SCRATCH_FPR  0
#define RSET_SCRATCH_GPR  (RSET_RANGE(RID_R52, RID_R59))
#define RSET_SCRATCH    (RSET_SCRATCH_GPR|RSET_SCRATCH_FPR)

#define REGARG_FIRSTGPR RID_R52
#define REGARG_LASTGPR  RID_R59
#define REGARG_NUMGPR   8
#define STACKARG_OFS (8*8)
/* wbs for pipe_call */
#define PIPE_WBS     0x1a

/* -- Spill slots --------------------------------------------------------- */

/* Spill slots are 32 bit wide.
**
** SPS_FIXED: Available fixed spill slots in interpreter frame.
** This definition must match with the *.dasc file(s).
**
** SPS_FIRST: First spill slot for general use.
*/
#define SPS_FIXED 0
#define SPS_FIRST 0
#define SPOFS_TMP 0x68

#define sps_scale(slot)   (4 * (int32_t)(slot))
#define sps_align(slot)   (((slot) - SPS_FIXED + 1) & ~1)

/* -- Exit state ---------------------------------------------------------- */

/* This definition must match with the *.dasc file(s). */
typedef struct {
  intptr_t gpr[RID_NUM_R];
  int32_t spill[256];
} ExitState;

/* Return the address of a per-trace exit stub. */
static LJ_AINLINE uint32_t *exitstub_trace_addr_(uint32_t *p, uint32_t exitno)
{
  while (*p == 0) p++; /* Skip NOP */
  return p;
}

/* Avoid dependence on lj_jit.h if only including lj_target.h. */
#define exitstub_trace_addr(T, exitno) \
  exitstub_trace_addr_((MCode *)((char *)(T)->mcode + (T)->szmcode), (exitno))

/* -- e2k bundle ---------------------------------------------------------- */

enum {
  /* HS */
  RES_ALS0    = 0x0001,
  RES_ALS1    = 0x0002,
  RES_ALS2    = 0x0004,
  RES_ALS3    = 0x0008,
  RES_ALS4    = 0x0010,
  RES_ALS5    = 0x0020,
  RES_CS0     = 0x0040,
  RES_CS1     = 0x0080,
  RES_AAS0    = 0x0100,
  RES_AAS1    = 0x0200,
  RES_AAS2    = 0x0400,
  RES_AAS3    = 0x0800,
  RES_AAS4    = 0x1000,
  RES_AAS5    = 0x2000,
  RES_LTS0    = 0x4000,
  RES_LTS1    = 0x8000,
  RES_LTS2    = 0x10000,
  RES_LTS3    = 0x20000,
  RES_PLS0    = 0x40000,
  RES_PLS1    = 0x80000,
  RES_PLS2    = 0x100000,
  RES_ALES0   = 0x200000,
  RES_ALES1   = 0x400000,
  RES_ALES2   = 0x800000,
  RES_ALES3   = 0x1000000,
  RES_ALES4   = 0x2000000,
  RES_ALES5   = 0x4000000,
  RES_SS      = 0x8000000,
  RES_CDS00   = 0x10000000,
  RES_CDS01   = 0x20000000,
  RES_CDS10   = 0x40000000,
  RES_CDS11   = 0x80000000,
  RES_CDS20   = 0x100000000,
  RES_CDS21   = 0x200000000,
  RES_MASK    = 0x3ffffffff,
  RES_INIT    = RES_MASK,
  RES_NONE    = 0,
  RES_ALS_012345 = RES_ALS0 | RES_ALS1 | RES_ALS2 | RES_ALS3 | RES_ALS4 | RES_ALS5,
  RES_ALS_0235   = RES_ALS0 | RES_ALS2 | RES_ALS3 | RES_ALS5,
  RES_ALS_0134   = RES_ALS0 | RES_ALS1 | RES_ALS3 | RES_ALS4,
  RES_ALS_03     = RES_ALS0 | RES_ALS3,
  RES_ALS_25     = RES_ALS2 | RES_ALS5,
  RES_ALS_ALL    = RES_ALS_012345,
  RES_ALES_ALL   = RES_ALES0 | RES_ALES1 | RES_ALES2 | RES_ALES3 | RES_ALES4 | RES_ALES5,
  RES_CS_ALL     = RES_CS0 | RES_CS1,
  RES_LTS_ALL    = RES_LTS0 | RES_LTS1 | RES_LTS2| RES_LTS3,
  RES_CDS_ALL    = RES_CDS00 | RES_CDS01 | RES_CDS10 | RES_CDS11 | RES_CDS20 | RES_CDS21,
  RES_CDS0       = RES_CDS00 | RES_CDS01,
  RES_CDS1       = RES_CDS10 | RES_CDS11,
  RES_CDS2       = RES_CDS20 | RES_CDS21,
  RES_ALS_SHIFT  = 0,
  RES_CS_SHIFT   = 6,
  RES_LTS_SHIFT  = 14,
  RES_ALES_SHIFT = 21,
  RES_CDS_SHIFT  = 28,
};

typedef struct {
  uint8_t f1;
  uint8_t f2;
  uint8_t f3;
  uint8_t f4;
//  uint8_t hs_pls;
  uint8_t hs_cds;
  uint32_t nop;
  uint64_t res;
  uint32_t ss;
  uint32_t als[6];
  uint32_t cs[2];
  uint16_t ales[6];
//  uint16_t aas[6];
  uint32_t lts[4];
//  uint32_t pls[3];
  uint16_t cds[6];
} E2kBundle;

typedef struct {
  int type;
  union {
    uint8_t u4;
    uint8_t u5;
    uint16_t u16;
    uint32_t u32;
    uint64_t u64;
    uint32_t regn;
  } value;
} E2kOperand;

/* -- Instructions -------------------------------------------------------- */

typedef union {
  uint32_t i;
  struct {
    uint32_t mdl     : 4;
    uint32_t lng     : 3;
    uint32_t nop     : 3;
    uint32_t lm      : 1;
    uint32_t x_s_sw  : 3;
    uint32_t c       : 2;
    uint32_t cds     : 2;
    uint32_t pls     : 2;
    uint32_t ales    : 6;
    uint32_t als     : 6;
  } fields;
} E2kHS;

typedef union {
  uint32_t i;
  struct {
    uint32_t ctcond  : 9;
    uint32_t x       : 1;
    uint32_t ctop    : 2;
    uint32_t aa      : 4;
    uint32_t alc     : 2;
    uint32_t abp     : 2;
    uint32_t type    : 1;
    uint32_t abn     : 2;
    uint32_t abg     : 2;
    uint32_t rp_lo   : 1;
    uint32_t vfdi    : 1;
    uint32_t rp_hi   : 1;
    uint32_t bap     : 1;
    uint32_t eap     : 1;
    uint32_t ipd     : 2;
  } fields;
} E2kSS;

typedef union {
  uint32_t i;
  struct {
    uint32_t dst     : 8;
    uint32_t src2    : 8;
    uint32_t src1    : 8;
    uint32_t cop     : 7;
    uint32_t spec    : 1;
  } fields;
} E2kAlopf1;

typedef union {
  uint32_t i;
  struct {
    uint32_t dst     : 8;
    uint32_t src2    : 8;
    uint32_t opce    : 8;
    uint32_t cop     : 7;
    uint32_t spec    : 1;
  } fields;
} E2kAlopf2;

typedef union {
  uint32_t i;
  struct {
    uint32_t src3    : 8;
    uint32_t src2    : 8;
    uint32_t src1    : 8;
    uint32_t cop     : 7;
    uint32_t spec    : 1;
  } fields;
} E2kAlopf3;

typedef union {
  uint32_t i;
  struct {
    uint32_t pdst    : 5;
    uint32_t cmpopce : 3;
    uint32_t src2    : 8;
    uint32_t src1    : 8;
    uint32_t cop     : 7;
    uint32_t spec    : 1;
  } fields;
} E2kAlopf7;

typedef union {
  uint32_t i;
  struct {
    uint32_t disp    : 28;
    uint32_t opc     : 2;
    uint32_t ctpr    : 2;
  } fields;
} E2kCopf2;

typedef union {
  uint32_t i;
  struct {
    uint32_t params  : 28;
    uint32_t opc     : 4;
  } fields;
} E2kC1f1;

typedef union {
  uint16_t i;
  struct {
    uint16_t pred    : 7;
    uint16_t neg     : 3;
    uint16_t mask    : 4;
    uint16_t opc     : 2;
  } fields;
} E2kCDS;

typedef enum {
  E2K_CONST = 0,
  E2K_CONST4 = 4,
  E2K_CONST5 = 5,
  E2K_CONST16 = 16,
  E2K_CONST32 = 32,
  E2K_CONST64 = 64,
  E2K_REG = 128,
  E2K_REG_R = 256,
  E2K_REG_B = 512,
  E2K_REG_G = 1024,
  E2K_REG_PRED = 2048,
  E2K_REG_CTPR = 4096,
  E2K_REG_RARG = 8192
} E2kOp;

#define REG_R 1
#define REG_B 2
#define REG_G 3
#define REG_CTPR 65
#define CONST_U4 4
#define CONST_U5 5
#define CONST_U16 16
#define CONST_U32 32
#define CONST_U64 64

/* -- Opcodes ------------------------------------------------------------- */

/* control operations */
#define OPC_DISP    0x0
#define OPC_IBRANCH 0x0
#define OPC_CALL    0x5
/* non-combined operations short */
#define OPC_ANDS   0x00
#define OPC_ANDD   0x01
#define OPC_ANDNS  0x02
#define OPC_ANDND  0x03
#define OPC_XORS   0x08
#define OPC_XORD   0x09
#define OPC_XORNS  0x0a
#define OPC_XORND  0x0b
#define OPC_SXT    0x0c
#define OPC_ADDS   0x10
#define OPC_ADDD   0x11
#define OPC_SUBS   0x12
#define OPC_SUBD   0x13
#define OPC_SHLS   0x18
#define OPC_SHLD   0x19
#define OPC_SARD   0x1d
#define OPC_GETFD  0x1f
#define OPC_CMPSB  0x20
#define OPC_CMPDB  0x21
#define OPC_STB    0x24
#define OPC_STH    0x25
#define OPC_STW    0x26
#define OPC_STD    0x27
#define OPC_FCMPDB 0x2f
#define OPC_FADDD  0x31
#define OPC_FSUBD  0x33
#define OPC_FMULD  0x39
#define OPC_FSTOS  0x3c
#define OPC_FDTOD  0x3d
#define OPC_FSTOD  0x3e
#define OPC_FDTOS  0x3f
#define OPC_MOVTD  0x61
#define OPC_LDB    0x64
#define OPC_LDH    0x65
#define OPC_LDW    0x66
#define OPC_LDD    0x67
/* non-combined operations long */
#define OPC_MULS   0x20
#define OPC_MULD   0x21
/* integer comparation opce */
#define CMPI_O     0x0
#define CMPI_B     0x1
#define CMPI_EQ    0x2
#define CMPI_BE    0x3
#define CMPI_S     0x4
#define CMPI_P     0x5
#define CMPI_LT    0x6
#define CMPI_LE    0x7
/* fp comporation opce */
#define CMPF_EQ    0x0
#define CMPF_LT    0x1
#define CMPF_LE    0x2
#define CMPF_UO    0x3
#define CMPF_NE    0x4
#define CMPF_NLT   0x5
#define CMPF_NLE   0x6
#define CMPF_OD    0x7
/* movt specificator opce */
#define MOVT_MV    0xc0
#define MOVT_MVC   0xc1
#define MOVT_MVR   0xc2
#define MOVT_MVRC  0xc3
/* convertation opc */
#define CO_FSTOISTR 0xc2
#define CO_FSTOIDTR 0xc2
#define CO_FDTOISTR 0xc2
#define CO_FDTOIDTR 0xc2
#define CO_ISTOFS   0xc4
#define CO_ISTOFD   0xc4
#define CO_IDTOFS   0xc4
#define CO_IDTOFD   0xc4
#define CO_FSTOFD   0xc6
#define CO_FDTOFS   0xc6
/* sxt codes */
#define SXT_BS      0x0
#define SXT_HS      0x1
#define SXT_WS      0x2
#define SXT_BZ      0x4
#define SXT_HZ      0x5
#define SXT_WZ      0x6
/* nop */
#define E2K_NOP     0x0

#endif
