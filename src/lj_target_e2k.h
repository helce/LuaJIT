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
    (RID2RSET(RID_SP)|RID2RSET(RID_DISPATCH)|RID2RSET(RID_LPC))
#define RSET_GPR    (RSET_RANGE(RID_R0, RID_B15+1) - RSET_FIXED)
#define RSET_PRED   (RSET_RANGE(RID_PRED0, RID_PRED3+1))
#define RSET_CTPR   (RSET_RANGE(RID_CTPR1, RID_CTPR3+1))
#define RSET_FPR    0
#define RSET_ALL    (RSET_GPR|RSET_PRED|RSET_CTPR)
#define RSET_INIT   RSET_ALL

/* In pipe state scratch registers are r52-r59 */
#define RSET_SCRATCH_FPR  0
#define RSET_SCRATCH_GPR  (RSET_RANGE(RID_R52, RID_R59+1))
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
#define SPS_FIXED 2
#define SPS_FIRST 2
#define SPOFS_TMP 0x0

#define sps_scale(slot)   (4 * (int32_t)(slot))
#define sps_align(slot)   (((slot) - SPS_FIXED + 3) & ~3)

/* -- Exit state ---------------------------------------------------------- */

/* This definition must match with the *.dasc file(s). */
typedef struct {
  intptr_t gpr[RID_NUM_R];
  int32_t spill[256];
} ExitState;

/* Highest exit + 1 indicates stack check. */
#define EXITSTATE_CHECKEXIT 1

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

typedef enum E2kResourceMask {
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
  RES_ALES_25    = RES_ALES2 | RES_ALES5,
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
} E2kResourceMask;

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

typedef union {
  uint16_t i;
  struct {
    uint16_t opce2   : 8;
    uint16_t opc2    : 8;
  } fields;
} E2kAlef2;

typedef union {
  uint16_t i;
  struct {
    uint16_t src3    : 8;
    uint16_t opc2    : 8;
  } fields;
} E2kAlef1;

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
} E2kOpT;

/* -- Opcodes ------------------------------------------------------------- */

#define E2K_DISP    0x0
#define E2K_IBRANCH 0x0
#define E2K_CALL    0x5
#define E2K_NOP     0x0
#define SXT_BS      0x0
#define SXT_HS      0x1
#define SXT_WS      0x2
#define SXT_BZ      0x4
#define SXT_HZ      0x5
#define SXT_WZ      0x6

typedef struct E2kOp {
  char *name;
  E2kResourceMask mask;
  uint32_t opc;
  uint32_t opce;
  uint32_t opc2;
  uint32_t opce2;
  // in_latency?
  // out_latency?
} E2kOp;

enum {
  /* ------------------------------------------------- */
  E2K_ANDS,     E2K_ANDD,     E2K_ANDNS,    E2K_ANDND,
  E2K_ORS,      E2K_ORD,      E2K_ORNS,     E2K_ORND,
  /* ------------------------------------------------- */
  E2K_XORS,     E2K_XORD,     E2K_XORNS,    E2K_XORND,
  E2K_SXT,
  /* ------------------------------------------------- */
  E2K_ADDS,     E2K_ADDD,     E2K_SUBS,     E2K_SUBD,
  E2K_SCLS,     E2K_SCLD,     E2K_SCRS,     E2K_SCRD,
  /* ------------------------------------------------- */
  E2K_SHLS,     E2K_SHLD,     E2K_SHRS,     E2K_SHRD,
  E2K_SARS,     E2K_SARD,     E2K_GETFS,    E2K_GETFD,
  /* ------------------------------------------------- */
  E2K_CMPBSB,   E2K_CMPESB,   E2K_CMPBESB,  E2K_CMPLSB,
  E2K_CMPLESB,  E2K_CMPBDB,   E2K_CMPEDB,   E2K_CMPBEDB,
  E2K_CMPLDB,   E2K_CMPLEDB,
  E2K_STB,      E2K_STH,      E2K_STW,      E2K_STD,
  /* ------------------------------------------------- */
  E2K_FCMPEQDB, E2K_FCMPLTDB, E2K_FCMPLEDB, E2K_FCMPNLTDB,
  E2K_FCMPNLEDB,
  /* ------------------------------------------------- */
  E2K_FADDS,    E2K_FADDD,    E2K_FSUBS,    E2K_FSUBD,
  /* ------------------------------------------------- */
  E2K_FMULS,    E2K_FMULD,    E2K_FSTOISTR, E2K_ISTOFS,
  E2K_FDTOIDTR, E2K_IDTOFD,   E2K_FSTOIDTR, E2K_ISTOFD,
  E2K_FSTOFD,   E2K_FDTOISTR, E2K_IDTOFS,   E2K_FDTOFS,
  /* ------------------------------------------------- */
  E2K_MOVTD,    E2K_LDB,      E2K_LDH,      E2K_LDW,
  E2K_LDD,
  /* ------------------------------------------------- */
  E2K_FDIVD,    E2K_FSQRTID,
  /* ------------------------------------------------- */
  E2K_FSQRTTD,
  /* ------------------------------------------------- */
  E2K_GETSP,
  /* ------------------------------------------------- */
  E2K_FDTOIFD,
  /* ------------------------------------------------- */
  E2K_PSHUFB
  /* ------------------------------------------------- */
};

static const E2kOp e2kop[] = {
/*  name        resources       opc   opce  opc2 opce2 */
/* non-combined operations short */
  { "ANDs",     RES_ALS_012345, 0x00, 0,    0,    0    },
  { "ANDd",     RES_ALS_012345, 0x01, 0,    0,    0    },
  { "ANDNs",    RES_ALS_012345, 0x02, 0,    0,    0    },
  { "ANDNd",    RES_ALS_012345, 0x03, 0,    0,    0    },
  { "ORs",      RES_ALS_012345, 0x04, 0,    0,    0    },
  { "ORd",      RES_ALS_012345, 0x05, 0,    0,    0    },
  { "ORNs",     RES_ALS_012345, 0x06, 0,    0,    0    },
  { "ORNd",     RES_ALS_012345, 0x07, 0,    0,    0    },
/* --------------------------------------------------- */
  { "XORs",     RES_ALS_012345, 0x08, 0,    0,    0    },
  { "XORd",     RES_ALS_012345, 0x09, 0,    0,    0    },
  { "XORNs",    RES_ALS_012345, 0x0a, 0,    0,    0    },
  { "XORNd",    RES_ALS_012345, 0x0b, 0,    0,    0    },
  { "SXT",      RES_ALS_012345, 0x0c, 0,    0,    0    },
/* --------------------------------------------------- */
  { "ADDs",     RES_ALS_012345, 0x10, 0,    0,    0    },
  { "ADDd",     RES_ALS_012345, 0x11, 0,    0,    0    },
  { "SUBs",     RES_ALS_012345, 0x12, 0,    0,    0    },
  { "SUBd",     RES_ALS_012345, 0x13, 0,    0,    0    },
  { "SCLs",     RES_ALS_012345, 0x14, 0,    0,    0    },
  { "SCLd",     RES_ALS_012345, 0x15, 0,    0,    0    },
  { "SCRs",     RES_ALS_012345, 0x16, 0,    0,    0    },
  { "SCRd",     RES_ALS_012345, 0x17, 0,    0,    0    },
/* --------------------------------------------------- */
  { "SHLs",     RES_ALS_012345, 0x18, 0,    0,    0    },
  { "SHLd",     RES_ALS_012345, 0x19, 0,    0,    0    },
  { "SHRs",     RES_ALS_012345, 0x1a, 0,    0,    0    },
  { "SHRd",     RES_ALS_012345, 0x1b, 0,    0,    0    },
  { "SARs",     RES_ALS_012345, 0x1c, 0,    0,    0    },
  { "SARd",     RES_ALS_012345, 0x1d, 0,    0,    0    },
  { "GETFs",    RES_ALS_012345, 0x1e, 0,    0,    0    },
  { "GETFd",    RES_ALS_012345, 0x1f, 0,    0,    0    },
/* --------------------------------------------------- */
  { "CMPBsb",   RES_ALS_0134,   0x20, 0x1,  0,    0    },
  { "CMPEsb",   RES_ALS_0134,   0x20, 0x2,  0,    0    },
  { "CMPBEsb",  RES_ALS_0134,   0x20, 0x3,  0,    0    },
  { "CMPLsb",   RES_ALS_0134,   0x20, 0x6,  0,    0    },
  { "CMPLEsb",  RES_ALS_0134,   0x20, 0x7,  0,    0    },
  { "CMPBdb",   RES_ALS_0134,   0x21, 0x1,  0,    0    },
  { "CMPEdb",   RES_ALS_0134,   0x21, 0x2,  0,    0    },
  { "CMPBEdb",  RES_ALS_0134,   0x21, 0x3,  0,    0    },
  { "CMPLdb",   RES_ALS_0134,   0x21, 0x6,  0,    0    },
  { "CMPLEdb",  RES_ALS_0134,   0x21, 0x7,  0,    0    },
  { "STb",      RES_ALS_25,     0x24, 0,    0,    0    },
  { "STh",      RES_ALS_25,     0x25, 0,    0,    0    },
  { "STw",      RES_ALS_25,     0x26, 0,    0,    0    },
  { "STd",      RES_ALS_25,     0x27, 0,    0,    0    },
/* --------------------------------------------------- */
  { "FCMPEQdb", RES_ALS_0134,   0x2f, 0x0,  0,    0    },
  { "FCMPLTdb", RES_ALS_0134,   0x2f, 0x1,  0,    0    },
  { "FCMPLEdb", RES_ALS_0134,   0x2f, 0x2,  0,    0    },
  { "FCMPNLTdb",RES_ALS_0134,   0x2f, 0x5,  0,    0    },
  { "FCMPNLEdb",RES_ALS_0134,   0x2f, 0x6,  0,    0    },
/* --------------------------------------------------- */
  { "FADDs",    RES_ALS_0134,   0x30, 0,    0,    0    },
  { "FADDd",    RES_ALS_0134,   0x31, 0,    0,    0    },
  { "FSUBs",    RES_ALS_0134,   0x32, 0,    0,    0    },
  { "FSUBd",    RES_ALS_0134,   0x33, 0,    0,    0    },
/* --------------------------------------------------- */
  { "FMULs",    RES_ALS_0134,   0x38, 0,    0,    0    },
  { "FMULd",    RES_ALS_0134,   0x39, 0,    0,    0    },
  { "FSTOIStr", RES_ALS_0134,   0x3c, 0xc2, 0,    0    },
  { "ISTOFS",   RES_ALS_0134,   0x3c, 0xc4, 0,    0    },
  { "FDTOIDtr", RES_ALS_0134,   0x3d, 0xc2, 0,    0    },
  { "IDTOFD",   RES_ALS_0134,   0x3d, 0xc4, 0,    0    },
  { "FSTOIDtr", RES_ALS_0134,   0x3e, 0xc2, 0,    0    },
  { "ISTOFD",   RES_ALS_0134,   0x3e, 0xc4, 0,    0    },
  { "FSTOFD",   RES_ALS_0134,   0x3e, 0xc6, 0,    0    },
  { "FDTOIStr", RES_ALS_0134,   0x3f, 0xc2, 0,    0    },
  { "IDTOFS",   RES_ALS_0134,   0x3f, 0xc4, 0,    0    },
  { "FDTOFS",   RES_ALS_0134,   0x3f, 0xc6, 0,    0    },
/* --------------------------------------------------- */
  { "MOVTd",    RES_ALS0,       0x61, 0xc0, 0,    0    },
  { "LDb",      RES_ALS_0235,   0x64, 0,    0,    0    },
  { "LDh",      RES_ALS_0235,   0x65, 0,    0,    0    },
  { "LDw",      RES_ALS_0235,   0x66, 0,    0,    0    },
  { "LDd",      RES_ALS_0235,   0x67, 0,    0,    0    },
/* --------------------------------------------------- */
  { "FDIVd",    RES_ALS5,       0x49, 0,    0x01, 0xc0 },
  { "FSQRTId",  RES_ALS5,       0x4d, 0xc0, 0x01, 0xc0 },
/* --------------------------------------------------- */
  { "FSQRTTd",  RES_ALS5,       0x51, 0,    0x01, 0xc0 },
/* --------------------------------------------------- */
  { "GETSP",    RES_ALS0,       0x58, 0xec, 0x01, 0xc0 },
/* --------------------------------------------------- */
  { "FDTOIFd",  RES_ALS_0134,   0x6d, 0,    0x01, 0xc0 },
/* --------------------------------------------------- */
  { "PSHUFB",   RES_ALS_0134,   0x4d, 0,    0x0f, 0    },
/* --------------------------------------------------- */
};

#endif
