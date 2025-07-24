/*
** E2K instruction emitter.
** Copyright (C) 2005-2025 Mike Pall. See Copyright Notice in luajit.h
*/

#define NIY __builtin_trap();

/* -- Bundling ------------------------------------------------------------ */

static uint32_t E2K_check_resource(ASMState *as, uint32_t mask)
{
  uint32_t res = as->bundle.res & mask;
  if (!res) {
    // TODO need to finalize first or just error.
    NIY
  }
  res = res & (-res);
  as->bundle.res &= ~res;
  return res;
}

static int E2K_add_alu_op(ASMState *as, uint32_t als_mask)
{
  uint32_t als = E2K_check_resource(as, als_mask);
  // convert to index
  int als_idx = 0;
  while (als >>= 1) {
    als_idx++;
  }
  return als_idx;
}

static uint32_t E2K_add_lts(ASMState *as, E2kOperand src)
{
  uint32_t mask = 0;
  if (src.type == CONST_U16) {
    mask = RES_LTS1|RES_LTS0;
  } else if (src.type == CONST_U32) {
    mask = RES_LTS2|RES_LTS1|RES_LTS0;
  } else {
    mask = RES_LTS3|RES_LTS2|RES_LTS1|RES_LTS0;
  }
  // TODO, manage halfsyls, now just lo part.
  uint32_t lts = E2K_check_resource(as, mask);
  // takes two lts
  if (src.type == CONST_U64) {
    E2K_check_resource(as, lts << 1);
  }

  lts >>= 14;
  // convert to index
  int lts_idx = 0;
  while (lts >>= 1) {
    lts_idx++;
  }
  switch (src.type) {
  case CONST_U16:
    as->bundle.lts[lts_idx] = (uint32_t)(src.value.u16); break;
  case CONST_U32:
    as->bundle.lts[lts_idx] = (uint32_t)(src.value.u32); break;
  case CONST_U64:
    as->bundle.lts[lts_idx] = (uint32_t)(src.value.u64);
    as->bundle.lts[lts_idx+1] = (uint32_t)(src.value.u64 >> 32);
    as->bundle.f4++;
    break;
  }
  as->bundle.f4++;
  return lts_idx;
} 

#define UT(t) u##t
#define E2K_CONST(t, val, op) \
  op.type = t; \
  op.value.UT(t) = val;

#define E2K_REG(t, val, op) \
  op.type = t; \
  op.value.regn = val;
  
static uint32_t E2K_SRC1(ASMState *as, E2kOperand src1)
{
  switch (src1.type) {
  case REG_B:
    return src1.value.regn - RID_B0;
  case REG_R:
    return (src1.value.regn - RID_R0) | 0x80;
  case REG_G:
    return (src1.value.regn - (RID_G16 + 16)) | 0xe0;
  case CONST_U4:
    return src1.value.u4 | 0xc0;
  case CONST_U5:
    return src1.value.u5 | 0xc0;
  default:
    lj_assertA(0, "bad type for src1 (%d)", src1.type);
    return 0;
  }
}

static uint32_t E2K_SRC2(ASMState *as, E2kOperand src2)
{
  switch (src2.type) {
  case REG_B:
    return src2.value.regn - RID_B0;
  case REG_R:
    return (src2.value.regn - RID_R0) | 0x80;
  case REG_G:
    return (src2.value.regn - (RID_G16 + 16)) | 0xe0;
  case CONST_U4:
    return src2.value.u4 | 0xc0;
  case CONST_U5:
    src2.type = CONST_U16;
    src2.value.u16 = src2.value.u5 & 0x1f;
    // fall through
  case CONST_U16:
    return 0xd0 + E2K_add_lts(as, src2);
  case CONST_U32:
    return 0xd8 + E2K_add_lts(as, src2);
  case CONST_U64:
    return 0xdc + E2K_add_lts(as, src2);
  default:
    lj_assertA(0, "bad type for src2 (%d)", src2.type);
    return 0;
  }
}

static uint32_t E2K_SRC3(ASMState *as, E2kOperand src3)
{
  switch (src3.type) {
  case REG_B:
    return src3.value.regn - RID_B0;
  case REG_R:
    return (src3.value.regn - RID_R0) | 0x80;
  case REG_G:
    return (src3.value.regn - (RID_G16 + 16)) | 0xe0;
  default:
    lj_assertA(0, "bad type for src3 (%d)", src3.type);
    return 0;
  }
}

static uint32_t E2K_DST(ASMState *as, E2kOperand dst)
{
  switch (dst.type) {
  case REG_B:
    return dst.value.regn - RID_B0;
  case REG_R:
    return (dst.value.regn - RID_R0) | 0x80;
  case REG_CTPR:
    return (dst.value.regn - (RID_CTPR1 + 1)) | 0xd0;
  case REG_G:
    return (dst.value.regn - (RID_G16 + 16)) | 0xe0;
  default:
    lj_assertA(0, "bad type for dst (%d)", dst.type);
    return 0;
  }
}

static uint32_t E2K_PDST(ASMState *as, Reg pred)
{
  return pred - RID_PRED1 + 1;
}

#define E2K_NOP(as, nops) \
  as->bundle.nop = nops

static void E2K_CT(ASMState *as, Reg ctpr)
{
  // TODO it takes not a full syl
  E2K_check_resource(as, RES_SS);
  E2kSS syl;
  syl.i = 0;
  syl.fields.ctcond = 0x20; // unconditional
  syl.fields.ctop = ctpr - RID_CTPR1 + 1;
  syl.fields.ipd = 3;

  as->bundle.ss = syl.i;
  as->bundle.f1++;
}

static void E2K_COPF2(ASMState *as, uint32_t opc, Reg ctpr, uintptr_t disp)
{
  E2K_check_resource(as, RES_CS0); 
  E2kCopf2 syl;
  syl.i = 0;
  syl.fields.disp = disp >> 3;
  syl.fields.opc = opc;
  syl.fields.ctpr = ctpr - RID_CTPR1 + 1;

  as->bundle.cs[0] = syl.i;
  as->bundle.f1++;
}

static void E2K_ALOPF1(ASMState *as, uint32_t spec, uint32_t cop,
                       E2kOperand src1, E2kOperand src2, E2kOperand dst, uint32_t als_mask)
{
  int als_idx = E2K_add_alu_op(as, als_mask);
  E2kAlopf1 syl;
  syl.i = 0;
  syl.fields.dst  = E2K_DST(as, dst);
  syl.fields.src2 = E2K_SRC2(as, src2);
  syl.fields.src1 = E2K_SRC1(as, src1);
  syl.fields.cop = cop;
  syl.fields.spec = spec;

  as->bundle.als[als_idx] = syl.i;
  as->bundle.f1++;
}

static void E2K_ALOPF3(ASMState *as, uint32_t spec, uint32_t cop,
                       E2kOperand src1, E2kOperand src2, E2kOperand src3, uint32_t als_mask)
{
  int als_idx = E2K_add_alu_op(as, als_mask);
  E2kAlopf1 syl;
  syl.i = 0;
  syl.fields.dst  = E2K_SRC3(as, src3);
  syl.fields.src2 = E2K_SRC2(as, src2);
  syl.fields.src1 = E2K_SRC1(as, src1);
  syl.fields.cop = cop;
  syl.fields.spec = spec;

  as->bundle.als[als_idx] = syl.i;
  as->bundle.f1++;
}

static void E2K_ALOPF7(ASMState *as, uint32_t spec, uint32_t cop, uint32_t opce,
                       E2kOperand src1, E2kOperand src2, Reg pred, uint32_t als_mask)
{
  int als_idx = E2K_add_alu_op(as, als_mask);
  E2kAlopf7 syl;
  syl.i = 0;
  syl.fields.pdst = E2K_PDST(as, pred);
  syl.fields.cmpopce = opce;
  syl.fields.src2 = E2K_SRC2(as, src2);
  syl.fields.src1 = E2K_SRC1(as, src1);
  syl.fields.cop = cop;
  syl.fields.spec = spec;

  as->bundle.als[als_idx] = syl.i;
  as->bundle.f1++;
}

/* -- Bundle -------------------------------------------------------------- */

static void emit_bundle_setup(ASMState *as)
{
  memset(&as->bundle, 0, sizeof(E2kBundle));
  as->bundle.res = RES_INIT;
  as->bundle.f1 = 1; // HS itself
}

static MCode *emit_bundle_finalize(ASMState *as, MCode *mxp)
{
  uint8_t f1 = as->bundle.f1;
  uint8_t f2 = as->bundle.f2;
  int half_pad = as->bundle.f3 & 0x1;
  uint8_t f3 = (as->bundle.f3 >> 1) + half_pad;
  uint8_t f4 = as->bundle.f4;
  uint8_t lng = f1 + f2 + f3 + f4;
  uint8_t hs_lng = (lng + 1) & -2;

  E2kHS hs;
  hs.i = 0;
  hs.fields.mdl = (uint32_t)(f1 + f2 - 1);
  hs.fields.lng = (uint32_t)(hs_lng >> 1) - 1;
  hs.fields.nop = (uint32_t)as->bundle.nop;
//  hs.fields.lm = (uint32_t)as->bundle.loop;
  uint32_t hs_x_s_sw = (as->bundle.res & RES_SS) ? 0 : 0x2;
  hs.fields.x_s_sw = hs_x_s_sw;
  uint32_t hs_c = (~as->bundle.res & RES_CS_ALL) >> RES_CS_SHIFT;
  hs.fields.c = hs_c;
//  hs.fields.cds = (uint32_t)as->bundle.hs_cds;
//  hs.fields.pls = (uint32_t)as->bundle.hs_pls;
  uint32_t hs_ales = (~as->bundle.res & RES_ALES_ALL) >> RES_ALES_SHIFT;
  hs.fields.ales = hs_ales;
  uint32_t hs_als = ~as->bundle.res & RES_ALS_ALL;
  hs.fields.als = hs_als;

  // cds, 16-bit halfsyls, not used 
  // pls, 32-bit syls, not used
  int used_lts = ((~as->bundle.res & RES_LTS_ALL) >> RES_LTS_SHIFT);
  for (int i = 0; i < 4; i++) {
    if (used_lts & (1 << i)) {
      *--mxp = as->bundle.lts[i];
    }
  }
  if (hs_lng != lng) {
    *--mxp = 0;
  }
  // aas, 16-bit syls, not used
  uint16_t *hmxp = (uint16_t *)mxp;
  if (half_pad) *--hmxp = 0;
  if (hs_ales & 0x10) *--hmxp = as->bundle.ales[4];
  if (hs_ales & 0x08) *--hmxp = as->bundle.ales[3];
  if (hs_ales & 0x02) *--hmxp = as->bundle.ales[1];
  if (hs_ales & 0x01) *--hmxp = as->bundle.ales[0];
  mxp = (MCode *)hmxp;
  if (hs_c & 0x02) *--mxp = as->bundle.cs[1];
  if (hs_c & 0x01) *--mxp = (as->bundle.cs[0] + (hs_lng >> 1));
  if (hs_als & 0x20) *--mxp = as->bundle.als[5];
  if (hs_als & 0x10) *--mxp = as->bundle.als[4];
  if (hs_als & 0x08) *--mxp = as->bundle.als[3];
  if (hs_als & 0x04) *--mxp = as->bundle.als[2];
  if (hs_als & 0x02) *--mxp = as->bundle.als[1];
  if (hs_als & 0x01) *--mxp = as->bundle.als[0];
  if (hs_x_s_sw) *--mxp = as->bundle.ss;
  *--mxp = hs.i; 

  emit_bundle_setup(as);
  return mxp;
}

/* -- Emit basic instructions --------------------------------------------- */

static void emit_loadu64(ASMState *as, Reg r, uint64_t u64)
{
  NIY
}

static void emit_loadk64(ASMState *as, Reg r, IRIns *ir)
{
  NIY
}

static int emit_canremat(IRRef ref)
{
  NIY
  return 0;
}

static void emit_opgl(ASMState *as, Reg r, void *p)
{
  NIY
}

#define emit_getgl(as, r, field) emit_opgl(as, r, (void *)&J2G(as->J)->field)
#define emit_setgl(as, r, field) emit_opgl(as, r, (void *)&J2G(as->J)->field)
#define emit_setvmstate(as, i) UNUSED(i)

static void emit_loadi(ASMState *as, Reg r, uint64_t u64)
{
  NIY
}

static void emit_loadofs(ASMState *as, IRIns *ir, Reg r, Reg base, int32_t ofs)
{
  NIY
}

static void emit_storeofs(ASMState *as, IRIns *ir, Reg r, Reg base, int32_t ofs)
{
  NIY
}

static void emit_movrr(ASMState *as, IRIns *ir, Reg dst, Reg src)
{
  NIY
}

static void emit_jmp(ASMState *as,  MCode *target)
{
  NIY
}

static void emit_addptr(ASMState *as, Reg r, int32_t ofs)
{
  NIY
}

#define emit_spsub(as, ofs) emit_addptr(as, 0, -(ofs))
