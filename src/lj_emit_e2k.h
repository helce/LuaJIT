/*
** E2K instruction emitter.
** Copyright (C) 2005-2025 Mike Pall. See Copyright Notice in luajit.h
*/

/* -- Bundling helpers ---------------------------------------------------- */

static uint64_t check_resource(ASMState *as, uint64_t mask)
{
  uint64_t res = as->bundle.res & mask;
  if (!res) {
    lj_assertA(0, "no available resources");
  }
  res = res & (-res);
  as->bundle.res &= ~res;
  return res;
}

static int get_sylidx(ASMState *as, uint64_t mask, uint64_t shift)
{
  uint64_t syl = check_resource(as, mask);
  syl = syl >> shift;
  int idx = 0;
  while(syl >>= 1)
    idx++;
  return idx;
}

#define checku4(x)  ((x) == (int32_t)(uint8_t)(x & 0xf))
#define checku5(x)  ((x) == (int32_t)(uint8_t)(x & 0x1f))

static intptr_t get_kval(ASMState *as, IRRef ref)
{
  IRIns *ir = IR(ref);
  if (ir->o == IR_KNULL || !irt_is64(ir->t)) {
    lj_assertA(ir->o == IR_KINT || ir->o == IR_KNULL,
               "bad 64 bit const IR op %d", ir->o);
    return ir->i; /* Sign-extended. */
  } else {
    return (intptr_t)ir_k64(ir)->u64;
  }
}

static E2kOpT get_reg_type(ASMState *as, intptr_t val)
{
  UNUSED(as);
  if (val <= RID_R15)
    return E2K_REG_R;
  else if (val <= RID_R59)
    return E2K_REG_RARG;
  else if (val <= RID_B15)
    return E2K_REG_B;
  else if (val <= RID_G19)
    return E2K_REG_G;
  else if (val <= RID_PRED3)
    return E2K_REG_PRED;
  else if (val <= RID_CTPR3)
    return E2K_REG_CTPR;
  else
    lj_assertA(0, "bad register (%d)", val);
  return 0;
}

static E2kOpT get_const_type(intptr_t val)
{
  if (checku4(val))
    return E2K_CONST4;
  else if(checku5(val))
    return E2K_CONST5;
  else if (checki16(val))
    return E2K_CONST16;
  else if (checki32(val))
    return E2K_CONST32;
  else
    return E2K_CONST64;
}

/* -- Bundling ------------------------------------------------------------ */

static void emit_bundle_setup(ASMState *as)
{
  memset(&as->bundle, 0, sizeof(E2kBundle));
  as->bundle.res = RES_INIT;
  as->bundle.f1 = 1; /* HS itself */
}

static MCode *emit_bundle_finalize(ASMState *as, MCode *mxp)
{
  uint32_t hs_x_s_sw = (as->bundle.res & RES_SS) ? 0 : 0x2;
  uint32_t hs_c = (~as->bundle.res & RES_CS_ALL) >> RES_CS_SHIFT;
  uint32_t hs_cds = (as->bundle.hs_cds + 1) & -2;
  uint32_t hs_ales = (~as->bundle.res & RES_ALES_ALL) >> RES_ALES_SHIFT;
  uint32_t hs_als = ~as->bundle.res & RES_ALS_ALL;

  uint8_t f1 = as->bundle.f1;
  uint8_t f2 = as->bundle.f2;
  int half_pad = as->bundle.f3 & 0x1;
  uint8_t f3 = (as->bundle.f3 >> 1) + half_pad;
  uint8_t f4 = as->bundle.f4 + (hs_cds >> 1);
  uint8_t lng = f1 + f2 + f3 + f4;
  uint8_t hs_lng = (lng + 1) & -2;

  E2kHS hs;
  hs.i = 0;
  hs.fields.mdl = (uint32_t)(f1 + f2 - 1);
  hs.fields.lng = (uint32_t)(hs_lng >> 1) - 1;
  hs.fields.nop = (uint32_t)as->bundle.nop;
  hs.fields.x_s_sw = hs_x_s_sw;
  hs.fields.c = hs_c;
  hs.fields.cds = hs_cds >> 1;
  hs.fields.ales = hs_ales;
  hs.fields.als = hs_als;

  /* CDS[0-5], 16-bit */
  uint16_t *hmxp = (uint16_t *)mxp;
  if (hs_cds > 4) {
    *--hmxp = as->bundle.cds[4];
    *--hmxp = as->bundle.cds[5];
  }
  if (hs_cds > 2) {
    *--hmxp = as->bundle.cds[2];
    *--hmxp = as->bundle.cds[3];
  }
  if (hs_cds > 0) {
    *--hmxp = as->bundle.cds[0];
    *--hmxp = as->bundle.cds[1];
  }
  mxp = (MCode *)hmxp;
  /* LTS[3-0], 32-bit, 16-bit half syls not implemented */
  int used_lts = ((~as->bundle.res & RES_LTS_ALL)  >> RES_LTS_SHIFT);
  for (int i = 0; i < 4; i++) {
    if (used_lts & (1 << i)) {
      *--mxp = as->bundle.lts[i];
    }
  }

  if (hs_lng != lng) *--mxp = 0; /* Align */
  /* ALES[0-1,3-4], 16-bit */
  hmxp = (uint16_t *)mxp;
  if (hs_ales & 0x10) *--hmxp = as->bundle.ales[4];
  if (hs_ales & 0x08) *--hmxp = as->bundle.ales[3];
  if (hs_ales & 0x02) *--hmxp = as->bundle.ales[1];
  if (hs_ales & 0x01) *--hmxp = as->bundle.ales[0];
  if (half_pad) *--hmxp = 0; /* Align */
  mxp = (MCode *)hmxp;
  /* CS[0-1], 32-bit */
  if (hs_c & 0x02) *--mxp = as->bundle.cs[1];
  if (hs_c & 0x01) {
    E2kCopf2 cs0 = { as->bundle.cs[0] };
    cs0.fields.disp = cs0.fields.disp + (hs_lng >> 1);
    *--mxp = cs0.i;
  }
  /* ALS[0-5], 32-bit */
  if (hs_als & 0x20) *--mxp = as->bundle.als[5];
  if (hs_als & 0x10) *--mxp = as->bundle.als[4];
  if (hs_als & 0x08) *--mxp = as->bundle.als[3];
  if (hs_als & 0x04) *--mxp = as->bundle.als[2];
  if (hs_als & 0x02) *--mxp = as->bundle.als[1];
  if (hs_als & 0x01) *--mxp = as->bundle.als[0];
  /* SS and HS */
  if (hs_x_s_sw) *--mxp = as->bundle.ss;
  *--mxp = hs.i; 

  emit_bundle_setup(as);
  return mxp;
}

/* -- Emit basic instructions --------------------------------------------- */

static uint32_t emit_lts(ASMState *as, E2kOpT type, uint64_t val)
{
  /* 16-bit halfsyls not managed yet, using lo part only */
  uint64_t mask = 0, lts = 0;
  int lts_idx = 0;
  if (type == E2K_CONST16) {
    mask = RES_LTS1|RES_LTS0;
  } else if (type == E2K_CONST32) {
    mask = RES_LTS3|RES_LTS2|RES_LTS1|RES_LTS0;
  } else {
    mask = RES_LTS2|RES_LTS1|RES_LTS0;
  }
  lts = check_resource(as, mask);
  if (type == E2K_CONST64) /* check 2 syls for 64-bit literal */
    check_resource(as, lts << 1);
  lts = lts >> RES_LTS_SHIFT;
  while (lts >>= 1)
    lts_idx++;

  switch (type) {
  case E2K_CONST16:
    as->bundle.lts[lts_idx] = (uint16_t)(val); break;
  case E2K_CONST32:
    as->bundle.lts[lts_idx] = (uint32_t)(val); break;
  case E2K_CONST64:
    as->bundle.lts[lts_idx] = (uint32_t)(val);
    as->bundle.lts[lts_idx+1] = (uint32_t)(val >> 32);
    as->bundle.f4++;
    break;
  }
  as->bundle.f4++;
  return lts_idx;
}

static uint32_t emit_src1(ASMState *as, E2kOpT type, intptr_t src1)
{
  UNUSED(as);
  if (type == E2K_REG) {
    switch (get_reg_type(as, src1)) {
    case E2K_REG_B:
      return src1 - RID_B0;
    case E2K_REG_R:
      return (src1 - RID_R0) | 0x80;
    case E2K_REG_RARG:
      return (src1 - RID_R52 + 52) | 0x80;
    case E2K_REG_G:
      return (src1 - RID_G16 + 16) | 0xe0;
    default:
      lj_assertA(0, "bad reg for src1 (%d)", src1);
      return 0;
    }
  } else {
    switch (get_const_type(src1)) {
    case E2K_CONST4: case E2K_CONST5:
      return src1 | 0xc0;
    default:
      lj_assertA(0, "bad type for src1 (%d)", type);
      return 0;
    }
  }
}

static uint32_t emit_src2(ASMState *as, E2kOpT type, intptr_t src2)
{
  if (type == E2K_REG) {
    switch (get_reg_type(as, src2)) {
    case E2K_REG_B:
      return src2 - RID_B0;
    case E2K_REG_R:
      return (src2 - RID_R0) | 0x80;
    case E2K_REG_RARG:
      return (src2 - RID_R52 + 52) | 0x80;
    case E2K_REG_G:
      return (src2 - RID_G16 + 16) | 0xe0;
    default:
      lj_assertA(0, "bad reg for src2 (%d)", src2);
      return 0;
    }
  } else {
    switch (get_const_type(src2)) {
    case E2K_CONST4:
      return src2 | 0xc0;
    case E2K_CONST5: case E2K_CONST16:
      return (emit_lts(as, E2K_CONST16, src2) | 0xd0);
    case E2K_CONST32:
      return (emit_lts(as, E2K_CONST32, src2) | 0xd8);
    case E2K_CONST64:
      return (emit_lts(as, E2K_CONST64, src2) | 0xdc);
    default:
      lj_assertA(0, "bad type for src2 (%d)", type);
      return 0;
    }
  }
}

static uint32_t emit_src3(ASMState *as, E2kOpT type, intptr_t src3)
{
  UNUSED(as);
  if (type == E2K_REG) {
    switch (get_reg_type(as, src3)) {
    case E2K_REG_B:
      return src3 - RID_B0;
    case E2K_REG_R:
      return (src3 - RID_R0) | 0x80;
    case E2K_REG_RARG:
      return (src3 - RID_R52 + 52) | 0x80;
    case E2K_REG_G:
      return (src3 - RID_G16 + 16) | 0xe0;
    default:
      lj_assertA(0, "bad reg for src3 (%d)", src3);
    }
  } else {
    lj_assertA(0, "bad type for src3 (%d)", type);
  }
}

static uint32_t emit_dst(ASMState *as, E2kOpT type, intptr_t dst)
{
  UNUSED(as);
  if (type == E2K_REG) {
    switch (get_reg_type(as, dst)) {
    case E2K_REG_B:
      return dst - RID_B0;
    case E2K_REG_R:
      return (dst - RID_R0) | 0x80;
    case E2K_REG_RARG:
      return (dst - RID_R52 + 52) | 0x80;
    case E2K_REG_CTPR:
      return (dst - RID_CTPR1 + 1) | 0xd0;
    case E2K_REG_G:
      return (dst - RID_G16 + 16) | 0xe0;
    default:
      lj_assertA(0, "bad reg for dst (%d)", dst);
    }
  } else {
    lj_assertA(0, "bad type for dst (%d)", type);
  }
}

static uint32_t emit_pdst(ASMState *as, E2kOpT type, intptr_t pred)
{
  UNUSED(as);
  if (type == E2K_REG_PRED) {
    return pred - RID_PRED1 + 1;
  } else {
    lj_assertA(0, "bad reg for pdst (%d)", pred);
    return 0;
  }
}

static int emit_alopf7(ASMState *as, MCode **p, uint32_t spec, uint32_t op,
                       uint32_t src1, uint32_t src2, uint32_t pred)
{
  uint64_t mask = e2kop[op].mask;
  int als_idx = get_sylidx(as, mask, RES_ALS_SHIFT);
  E2kAlopf7 syl;
  syl.i = 0;
  syl.fields.pdst = pred;
  syl.fields.cmpopce = e2kop[op].opce;
  syl.fields.src2 = src2;
  syl.fields.src1 = src1;
  syl.fields.cop = e2kop[op].opc;
  syl.fields.spec = spec;

  as->bundle.als[als_idx] = syl.i;
  as->bundle.f1++;
  if (p) *p = emit_bundle_finalize(as, *p);
  return als_idx;
}

static int emit_alopf3(ASMState *as, MCode **p, uint32_t spec, uint32_t op,
                        uint64_t src1, uint32_t src2, uint32_t src3)
{
  uint64_t mask = e2kop[op].mask;
  int als_idx = get_sylidx(as, mask, RES_ALS_SHIFT);
  E2kAlopf3 syl;
  syl.i = 0;
  syl.fields.src3  = src3;
  syl.fields.src2 = src2;
  syl.fields.src1 = src1;
  syl.fields.cop = e2kop[op].opc;
  syl.fields.spec = spec;

  as->bundle.als[als_idx] = syl.i;
  as->bundle.f1++;
  if (p) *p = emit_bundle_finalize(as, *p);
  return als_idx;
}

static int emit_alopf2(ASMState *as, MCode **p, uint32_t spec, uint32_t op,
                       uint32_t src2, uint32_t dst)
{
  uint64_t mask = e2kop[op].mask;
  int als_idx = get_sylidx(as, mask, RES_ALS_SHIFT);
  E2kAlopf2 syl;
  syl.i = 0;
  syl.fields.dst  = dst;
  syl.fields.src2 = src2;
  syl.fields.opce = e2kop[op].opce;
  syl.fields.cop = e2kop[op].opc;
  syl.fields.spec = spec;

  as->bundle.als[als_idx] = syl.i;
  as->bundle.f1++;
  if (p) *p = emit_bundle_finalize(as, *p);
  return als_idx;
}

static int emit_alopf1(ASMState *as, MCode **p, uint32_t spec, uint32_t op,
                        uint32_t src1, uint32_t src2, uint32_t dst)
{
  uint64_t mask = e2kop[op].mask;
  int als_idx = get_sylidx(as, mask, RES_ALS_SHIFT);
  E2kAlopf1 syl;
  syl.i = 0;
  syl.fields.dst  = dst;
  syl.fields.src2 = src2;
  syl.fields.src1 = src1;
  syl.fields.cop = e2kop[op].opc;
  syl.fields.spec = spec;

  as->bundle.als[als_idx] = syl.i;
  as->bundle.f1++;
  if (p) *p = emit_bundle_finalize(as, *p);
  return als_idx;
}

static void emit_alef2(ASMState *as, uint32_t op, int als_idx)
{
  /* No combined operations on 2 and 5 channels */
  int res = 1 << (RES_ALES_SHIFT + als_idx);
  check_resource(as, res);
  if (!(res & RES_ALES_25)) {
    E2kAlef2 syl;
    syl.i = 0;
    syl.fields.opce2 = e2kop[op].opce2;
    syl.fields.opc2 = e2kop[op].opc2;
    as->bundle.ales[als_idx] = syl.i;
    as->bundle.f3++;
  }
}

static void emit_alef1(ASMState *as, uint32_t op, uint32_t src3, int als_idx)
{
  /* No combined operations on 2 and 5 channels */
  int res = 1 << (RES_ALES_SHIFT + als_idx);
  check_resource(as, res);
  if (!(res & RES_ALES_25)) {
    E2kAlef1 syl;
    syl.i = 0;
    syl.fields.src3 = (uint16_t)src3;
    syl.fields.opc2 = e2kop[op].opc2;
    as->bundle.ales[als_idx] = syl.i;
    as->bundle.f3++;
  }
}

static int emit_alopf12(ASMState *as, MCode **p, uint32_t spec, uint32_t op,
                        uint32_t src2, uint32_t dst)
{
  int als_idx = emit_alopf2(as, 0, spec, op, src2, dst);
  emit_alef2(as, op, als_idx);
  if (p) *p = emit_bundle_finalize(as, *p);
  return als_idx;
}

static int emit_alopf21(ASMState *as, MCode **p, uint32_t spec, uint32_t op,
                        uint32_t src1, uint32_t src2, uint32_t src3, uint32_t dst)
{
  int als_idx = emit_alopf1(as, 0, spec, op, src1, src2, dst);
  emit_alef1(as, op, src3, als_idx);
  if (p) *p = emit_bundle_finalize(as, *p);
  return als_idx;
}

static int emit_alopf11(ASMState *as, MCode **p, uint32_t spec, uint32_t op,
                        uint32_t src1, uint32_t src2, uint32_t dst)
{
  int als_idx = emit_alopf1(as, 0, spec, op, src1, src2, dst);
  emit_alef2(as, op, als_idx);
  if (p) *p = emit_bundle_finalize(as, *p);
  return als_idx;
}

static void emit_cds(ASMState *as, int opc, int als, Reg pred, int inverted, MCode **p)
{
  int cds_idx = get_sylidx(as, RES_CDS_ALL, RES_CDS_SHIFT);
  E2kCDS syl;
  syl.i = 0;
  syl.fields.pred = (pred - RID_PRED0)|0x60;
  switch (1 << als) {
  case 0x1: case 0x8:
     if (inverted) syl.fields.neg = 1;
     syl.fields.mask = 1;
     break;
  case 0x2: case 0x10:
     if (inverted) syl.fields.neg = 2;
     syl.fields.mask = 2;
     break;
  case 0x4: case 0x20:
     if (inverted) syl.fields.neg = 4;
     syl.fields.mask = 4;
     break;
  }
  if (als >= 3) opc++;
  syl.fields.opc = opc;
  as->bundle.cds[cds_idx] = syl.i;
  as->bundle.hs_cds++;
  if (p) *p = emit_bundle_finalize(as, *p);
}

#define emit_rlp(as, als, pred, inv, p) \
  emit_cds(as, 0, als, pred, inv, p)
#define emit_mrgc(as, als, pred, inv, p) \
  emit_cds(as, 2, als, pred, inv, p)
#define ISRC1(src1) emit_src1(as, E2K_CONST, src1)
#define RSRC1(src1) emit_src1(as, E2K_REG, src1)
#define ISRC2(src2) emit_src2(as, E2K_CONST, src2)
#define RSRC2(src2) emit_src2(as, E2K_REG, src2)
#define RSRC3(src3) emit_src3(as, E2K_REG, src3)
#define RDST(dst)  emit_dst(as, E2K_REG, dst)
#define PDST(pred) emit_pdst(as, E2K_REG_PRED, pred)
#define emit_alopf7_rr(as, spec, op, src1, src2, pred, p) \
  emit_alopf7(as, p, spec, op, RSRC1(src1), RSRC2(src2), PDST(pred))
#define emit_alopf7_ri(as, spec, op, src1, src2, pred, p) \
  emit_alopf7(as, p, spec, op, RSRC1(src1), ISRC2(src2), PDST(pred))
#define emit_alopf3_ri(as, spec, op, src1, src2, src3, p) \
  emit_alopf3(as, p, spec, op, RSRC1(src1), ISRC2(src2), RSRC3(src3))
#define emit_alopf12_i(as, spec, op, src2, dst, p) \
  emit_alopf12(as, p, spec, op, ISRC2(src2), RDST(dst))
#define emit_alopf12_r(as, spec, op, src2, dst, p) \
  emit_alopf12(as, p, spec, op, RSRC2(src2), RDST(dst))
#define emit_alopf2_i(as, spec, op, src2, dst, p) \
  emit_alopf2(as, p, spec, op, ISRC2(src2), RDST(dst))
#define emit_alopf2_r(as, spec, op, src2, dst, p) \
  emit_alopf2(as, p, spec, op, RSRC2(src2), RDST(dst))
#define emit_alopf21_rrr(as, spec, op, src1, src2, src3, dst, p) \
  emit_alopf21(as, p, spec, op, RSRC1(src1), RSRC2(src2), RSRC3(src3), RDST(dst))
#define emit_alopf11_rr(as, spec, op, src1, src2, dst, p) \
  emit_alopf11(as, p, spec, op, RSRC1(src1), RSRC2(src2), RDST(dst))
#define emit_alopf11_ir(as, spec, op, src1, src2, dst, p) \
  emit_alopf11(as, p, spec, op, ISRC1(src1), RSRC2(src2), RDST(dst))
#define emit_alopf11_ri(as, spec, op, src1, src2, dst, p) \
  emit_alopf11(as, p, spec, op, RSRC1(src1), ISRC2(src2), RDST(dst))
#define emit_alopf11_ii(as, spec, op, src1, src2, dst, p) \
  emit_alopf11(as, p, spec, op, ISRC1(src1), ISRC2(src2), RDST(dst))
#define emit_alopf1_rr(as, spec, op, src1, src2, dst, p) \
  emit_alopf1(as, p, spec, op, RSRC1(src1), RSRC2(src2), RDST(dst))
#define emit_alopf1_ir(as, spec, op, src1, src2, dst, p) \
  emit_alopf1(as, p, spec, op, ISRC1(src1), RSRC2(src2), RDST(dst))
#define emit_alopf1_ri(as, spec, op, src1, src2, dst, p) \
  emit_alopf1(as, p, spec, op, RSRC1(src1), ISRC2(src2), RDST(dst))
#define emit_alopf1_ii(as, spec, op, src1, src2, dst, p) \
  emit_alopf1(as, p, spec, op, ISRC1(src1), ISRC2(src2), RDST(dst))
#define emit_snapno(as, snapno, p) \
  emit_alopf1(as, p, 0, E2K_ADDD, emit_src1(as, E2K_CONST, 0), \
               emit_lts(as, E2K_CONST32, (intptr_t)snapno) | 0xd8, \
               emit_dst(as, E2K_REG, RID_TMP))
#define emit_nop(as, nops) \
  as->bundle.nop = nops

/* -- Emit loads/stores --------------------------------------------------- */

#define dispofs(as, k) \
  ((intptr_t)((uintptr_t)(k) - (uintptr_t)J2GG(as->J)->dispatch))

/* Prefer rematerialization of BASE/L from global_State over spills. */
#define emit_canremat(ref)  ((ref) <= REF_BASE)

/* Load a 64 bit constant into a GPR. */
static void emit_loadu64(ASMState *as, Reg r, uint64_t u64)
{
  emit_alopf1_ii(as, 0, E2K_ADDD, 0, u64, r, &as->mcp);
}

static void emit_loadk64(ASMState *as, Reg r, IRIns *ir)
{
  const uint64_t *k = &ir_k64(ir)->u64;
  emit_loadu64(as, r, *k);
}

static void emit_ldd(ASMState *as, Reg dest, void *addr)
{
  emit_alopf1_ri(as, 0, E2K_LDD, RID_DISPATCH,
                 (intptr_t)dispofs(as, addr), dest, &as->mcp);
}

static void emit_std(ASMState *as, Reg src, void *addr)
{
  emit_alopf3_ri(as, 0, E2K_STD, RID_DISPATCH, (intptr_t)dispofs(as, addr),
                 src, &as->mcp);
}

/* Load a constant address into a GPR. */
#define emit_loada(as, r, addr)   emit_loadu64(as, (r), u64ptr((addr)))
/* Load a 32 bit constant into a GPR. */
#define emit_loadi(as, r, i)      emit_loadu64(as, (r), (intptr_t)i)

/* Get/set global_State fields. */
#define emit_getgl(as, r, field) emit_ldd(as, r, (void *)&J2G(as->J)->field)
#define emit_setgl(as, r, field) emit_std(as, r, (void *)&J2G(as->J)->field)

/* Trace number is determined from per-trace exit stubs. */
#define emit_setvmstate(as, i) UNUSED(i)

/* -- Emit control-flow instructions -------------------------------------- */

/* Label for internal jumps. */
typedef MCode *MCLabel;

/* Return label pointing to current PC. */
#define emit_label(as)    ((as)->mcp)

static void emit_ct(ASMState *as, Reg ctpr, Reg pred, int inverted, MCode **p)
{
  check_resource(as, RES_SS); /* Uses only part of RES_SS */
  E2kSS syl;
  syl.i = 0;
  if (pred) { /* RID_PREDX is nonnull  */
    if (inverted) {
      syl.fields.ctcond = 0x60 + (pred - RID_PRED0);
    } else {
      syl.fields.ctcond = 0x40 + (pred - RID_PRED0);
    }
  } else {
    syl.fields.ctcond = 0x20; /* unconditional */
  }
  if (ctpr)  /* RID_CTPRX is nonnull */
    syl.fields.ctop = ctpr - RID_CTPR1 + 1;
  syl.fields.ipd = 3;

  as->bundle.ss = syl.i;
  as->bundle.f1++;
  if (p) *p = emit_bundle_finalize(as, *p);
}

static void emit_call(ASMState *as, Reg ctpr, Reg pred,
                      int inverted, int wbs, MCode **p)
{
  emit_ct(as, ctpr, pred, inverted, 0);
  check_resource(as, RES_CS1);
  E2kC1f1 syl;
  syl.i = 0;
  syl.fields.opc = E2K_CALL;
  syl.fields.params = wbs;
  as->bundle.cs[1] = syl.i;
  as->bundle.f2++;
  if (p) *p = emit_bundle_finalize(as, *p);
}

static void emit_copf2(ASMState *as, uint32_t opc, Reg ctpr,
                       uintptr_t disp, MCode **p)
{
  check_resource(as, RES_CS0);
  E2kCopf2 syl;
  syl.i = 0;
  syl.fields.disp = disp >> 3;
  syl.fields.opc = opc;
  if (ctpr) /* RID_CTPRX is nonnull */
    syl.fields.ctpr = ctpr - RID_CTPR1 + 1;

  as->bundle.cs[0] = syl.i;
  as->bundle.f1++;
  if (p) *p = emit_bundle_finalize(as, *p);
}


// 31 signed bits
#define DISP_MIN 0xffffffffc0000000
#define DISP_MAX 0x000000003fffffff

static void emit_prepcall(ASMState *as, Reg ctpr,
                          ASMFunction target, MCode **p)
{
  ptrdiff_t disp = (ptrdiff_t)((void *) target - (void *)as->mcp);
  /* check disp fits in short range*/
  if ((intptr_t)disp < (intptr_t)DISP_MAX && (intptr_t)disp > (intptr_t)DISP_MIN ) {
    emit_copf2(as, E2K_DISP, ctpr, disp, p);
  } else { /* Target out of range; need indirect call. */
    emit_alopf2_i(as, 0, E2K_MOVTD, (intptr_t)target, ctpr, p);
  }
}

static void emit_ibranch(ASMState *as, uintptr_t disp, Reg pred,
                         int inverted, MCode **p)
{
  emit_ct(as, 0, pred, inverted, 0);
  emit_copf2(as, E2K_IBRANCH, 0, disp, p);
}

static void emit_jmp(ASMState *as,  MCode *target)
{
  emit_ibranch(as, (ptrdiff_t)((void *)target - (void *)as->mcp),
               0, 0, &as->mcp);
}

/* -- Emit generic operations --------------------------------------------- */

/* argument extension */
static void emit_ext(ASMState *as, Reg dst, Reg src, int ext) {
  emit_alopf1_ir(as, 0, E2K_SXT, ext, src, dst, &as->mcp);
}

/* Generic move between two regs. */
static void emit_movrr(ASMState *as, IRIns *ir, Reg dst, Reg src)
{
  UNUSED(ir);
  emit_alopf1_ri(as, 0, E2K_ADDD, src, 0, dst, &as->mcp);
}

/* Generic load of register with base and (small) offset address. */
static void emit_loadofs(ASMState *as, IRIns *ir, Reg r, Reg base, int32_t ofs)
{
  emit_alopf1_ri(as, 0, irt_is64(ir->t) ? E2K_LDD : E2K_LDW,
                 base, ofs, r, &as->mcp);
}

/* Generic store of register with base and (small) offset address. */
static void emit_storeofs(ASMState *as, IRIns *ir, Reg r, Reg base, int32_t ofs)
{
  emit_alopf3_ri(as, 0, irt_is64(ir->t) ? E2K_STD : E2K_STW,
                 base, ofs, r, &as->mcp);
}

/* Add offset to pointer. */
static void emit_addptr(ASMState *as, Reg r, int32_t ofs)
{
  if (ofs) {
    emit_alopf1_ri(as, 0, E2K_ADDD, r, ofs, r, &as->mcp);
  }
}

/* Get additional stack space. */
static void emit_spsub(ASMState *as, int32_t ofs)
{
  if (ofs) {
    emit_alopf12_i(as, 0, E2K_GETSP, -ofs, RID_SP, &as->mcp);
  }
}
