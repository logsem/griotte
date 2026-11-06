	.attribute	4, 16
	.attribute	5, "rv32e2p0_m2p0_c2p0_zmmul1p0_zca1p0_xcheri0p0_xcheriot1p0_xcheripurecap0p0"
	.file	"main.cc"
	.section	.text._Z1fPPvPU10chericcallFvS0_S0_E,"ax",@progbits
	.globl	_Z1fPPvPU10chericcallFvS0_S0_E  # -- Begin function _Z1fPPvPU10chericcallFvS0_S0_E
	.p2align	1
	.type	_Z1fPPvPU10chericcallFvS0_S0_E,@function
_Z1fPPvPU10chericcallFvS0_S0_E:         # @_Z1fPPvPU10chericcallFvS0_S0_E
# %bb.0:
	ct.cincoffset	sp, sp, -32
	ct.csc	ra, 24(sp)                      # 8-byte Folded Spill
	ct.cgettag	a3, a0
	beqz	a3, .LBB0_9
# %bb.1:
	ct.cmove	a2, a1
	ct.cgetperm	a1, a0
	andi	a1, a1, 32
	beqz	a1, .LBB0_9
# %bb.2:
	ct.cgetbase	a3, a0
	ct.cgetlen	a1, a0
	ct.cgetbase	a4, sp
	add	a1, a1, a3
	bgeu	a3, a4, .LBB0_4
# %bb.3:
	addi	a5, a1, -1
	bltu	a5, a4, .LBB0_5
	j	.LBB0_9
.LBB0_4:
	ct.cgetlen	a5, sp
	add	a4, a4, a5
	addi	a4, a4, -1
	bgeu	a4, a3, .LBB0_9
.LBB0_5:
	ct.csetaddr	a0, a0, a3
	bgeu	a0, a1, .LBB0_8
.LBB0_6:                                # =>This Inner Loop Header: Depth=1
	ct.clc	a3, 0(a0)
	ct.cgettag	a3, a3
	bnez	a3, .LBB0_9
# %bb.7:                                #   in Loop: Header=BB0_6 Depth=1
	ct.cincoffset	a0, a0, 8
	bltu	a0, a1, .LBB0_6
.LBB0_8:
	li	a1, 42
	ct.csw	a1, 20(sp)
	ct.cincoffset	a1, sp, 8
	ct.csw	zero, 12(sp)
	ct.csw	zero, 8(sp)
	ct.csetbounds	a1, a1, 8
	ct.cmove	t1, a2
.LBB0_10:                               # Label of block must be emitted
	ct.auipcc	t2, %cheriot_compartment_hi(.compartment_switcher)
	ct.clc	t2, %cheriot_compartment_lo_i(.LBB0_10)(t2)
	ct.cjalr	t2
	ct.clw	a0, 20(sp)
	li	a1, 42
.LBB0_11:                               # Label of block must be emitted
	ct.auipcc	t2, %cheriot_compartment_hi(__library_import_libcalls__Z14griotte_assertii)
	ct.clc	t2, %cheriot_compartment_lo_i(.LBB0_11)(t2)
	ct.cjalr	t2
	li	a0, 0
	li	a1, 0
	ct.clc	ra, 24(sp)                      # 8-byte Folded Reload
	ct.cincoffset	sp, sp, 32
	ct.cret
.LBB0_9:
	unimp
.Lfunc_end0:
	.size	_Z1fPPvPU10chericcallFvS0_S0_E, .Lfunc_end0-_Z1fPPvPU10chericcallFvS0_S0_E
                                        # -- End function
	.section	.text._Z5entryv,"ax",@progbits
	.globl	_Z5entryv                       # -- Begin function _Z5entryv
	.p2align	1
	.type	_Z5entryv,@function
_Z5entryv:                              # @_Z5entryv
# %bb.0:
	ct.cincoffset	sp, sp, -16
	ct.csc	ra, 8(sp)                       # 8-byte Folded Spill
.LBB1_2:                                # Label of block must be emitted
	ct.auipcc	t1, %cheriot_compartment_hi(__import_C__Z3advv)
	ct.clc	t1, %cheriot_compartment_lo_i(.LBB1_2)(t1)
.LBB1_1:                                # Label of block must be emitted
	ct.auipcc	t2, %cheriot_compartment_hi(.compartment_switcher)
	ct.clc	t2, %cheriot_compartment_lo_i(.LBB1_1)(t2)
	ct.cjalr	t2
	li	a0, 0
	li	a1, 0
	ct.clc	ra, 8(sp)                       # 8-byte Folded Reload
	ct.cincoffset	sp, sp, 16
	ct.cret
.Lfunc_end1:
	.size	_Z5entryv, .Lfunc_end1-_Z5entryv
                                        # -- End function
	.type	__default_malloc_capability,@object # @__default_malloc_capability
	.section	.sealed_objects,"awG",@progbits,__default_malloc_capability,comdat
	.weak	__default_malloc_capability
	.p2align	3, 0x0
__default_malloc_capability:
	.word	__export.sealing_type.allocator.MallocKey
	.word	0                               # 0x0
	.word	4096                            # 0x1000
	.word	0                               # 0x0
	.zero	16
	.size	__default_malloc_capability, 32

	.ident	"clang version 21.1.7 (CHERIoT-Platform/llvm-project-DLLVM_VC_REVISION=2b6c51c910ebe464ae686520aa2ba253b9e5f19e)"
	.section	".note.GNU-stack","",@progbits
	.addrsig
	.addrsig_sym __export.sealing_type.allocator.MallocKey
	.addrsig_sym __default_malloc_capability
	.section	.compartment_exports,"aR",@progbits
	.type	__export_main__Z1fPPvPU10chericcallFvS0_S0_E,@object
	.globl	__export_main__Z1fPPvPU10chericcallFvS0_S0_E
	.p2align	2, 0x0
__export_main__Z1fPPvPU10chericcallFvS0_S0_E:
	.half	_Z1fPPvPU10chericcallFvS0_S0_E-__compartment_pcc_start
	.byte	4
	.byte	10
	.size	__export_main__Z1fPPvPU10chericcallFvS0_S0_E, 4
	.type	__export_main__Z5entryv,@object
	.globl	__export_main__Z5entryv
	.p2align	2, 0x0
__export_main__Z5entryv:
	.half	_Z5entryv-__compartment_pcc_start
	.byte	2
	.byte	8
	.size	__export_main__Z5entryv, 4
	.section	.compartment_imports._Z14griotte_assertii,"aG",@progbits,__library_import_libcalls__Z14griotte_assertii,comdat
	.type	__library_import_libcalls__Z14griotte_assertii,@object
	.weak	__library_import_libcalls__Z14griotte_assertii
	.p2align	3, 0x0
__library_import_libcalls__Z14griotte_assertii:
	.word	__library_export_libcalls__Z14griotte_assertii+1
	.word	0
	.size	__library_import_libcalls__Z14griotte_assertii, 8
	.section	.compartment_imports._Z3advv,"aG",@progbits,__import_C__Z3advv,comdat
	.type	__import_C__Z3advv,@object
	.weak	__import_C__Z3advv
	.p2align	3, 0x0
__import_C__Z3advv:
	.word	__export_C__Z3advv
	.word	0
	.size	__import_C__Z3advv, 8
