	.attribute	4, 16
	.attribute	5, "rv32e2p0_m2p0_c2p0_zmmul1p0_zca1p0_xcheri0p0_xcheriot1p0_xcheripurecap0p0"
	.file	"main.cc"
	.section	.text._Z3runv,"ax",@progbits
	.globl	_Z3runv                         # -- Begin function _Z3runv
	.p2align	1
	.type	_Z3runv,@function
_Z3runv:                                # @_Z3runv
# %bb.0:
	ct.cincoffset	sp, sp, -16
	ct.csc	ra, 8(sp)                       # 8-byte Folded Spill
	ct.csc	s0, 0(sp)                       # 8-byte Folded Spill
.LBB0_2:                                # Label of block must be emitted
	ct.auipcc	t1, %cheriot_compartment_hi(__import_adv__Z3advv)
	ct.clc	t1, %cheriot_compartment_lo_i(.LBB0_2)(t1)
.LBB0_1:                                # Label of block must be emitted
	ct.auipcc	t2, %cheriot_compartment_hi(.compartment_switcher)
	ct.clc	t2, %cheriot_compartment_lo_i(.LBB0_1)(t2)
	ct.cjalr	t2
.LBB0_3:                                # Label of block must be emitted
	ct.auicgp	s0, %cheriot_compartment_hi(_ZL1x)
	ct.cincoffset	s0, s0, %cheriot_compartment_lo_i(.LBB0_3)
	ct.csetbounds	s0, s0, %cheriot_compartment_size(_ZL1x)
	ct.cincoffset	a0, s0, 4
.LBB0_5:                                # Label of block must be emitted
	ct.auipcc	t1, %cheriot_compartment_hi(__import_stats__Z10stats_readPi)
	ct.clc	t1, %cheriot_compartment_lo_i(.LBB0_5)(t1)
.LBB0_4:                                # Label of block must be emitted
	ct.auipcc	t2, %cheriot_compartment_hi(.compartment_switcher)
	ct.clc	t2, %cheriot_compartment_lo_i(.LBB0_4)(t2)
	ct.cjalr	t2
	li	a1, 42
.LBB0_6:                                # Label of block must be emitted
	ct.auipcc	t2, %cheriot_compartment_hi(__library_import_libcalls__Z14griotte_assertii)
	ct.clc	t2, %cheriot_compartment_lo_i(.LBB0_6)(t2)
	ct.cjalr	t2
	ct.ccleartag	a0, s0
.LBB0_8:                                # Label of block must be emitted
	ct.auipcc	t1, %cheriot_compartment_hi(__import_stats__Z10stats_readPi)
	ct.clc	t1, %cheriot_compartment_lo_i(.LBB0_8)(t1)
.LBB0_7:                                # Label of block must be emitted
	ct.auipcc	t2, %cheriot_compartment_hi(.compartment_switcher)
	ct.clc	t2, %cheriot_compartment_lo_i(.LBB0_7)(t2)
	ct.cjalr	t2
	li	a1, -1
.LBB0_9:                                # Label of block must be emitted
	ct.auipcc	t2, %cheriot_compartment_hi(__library_import_libcalls__Z14griotte_assertii)
	ct.clc	t2, %cheriot_compartment_lo_i(.LBB0_9)(t2)
	ct.cjalr	t2
	ct.cmove	a0, s0
.LBB0_11:                               # Label of block must be emitted
	ct.auipcc	t1, %cheriot_compartment_hi(__import_stats__Z10stats_readPi)
	ct.clc	t1, %cheriot_compartment_lo_i(.LBB0_11)(t1)
.LBB0_10:                               # Label of block must be emitted
	ct.auipcc	t2, %cheriot_compartment_hi(.compartment_switcher)
	ct.clc	t2, %cheriot_compartment_lo_i(.LBB0_10)(t2)
	ct.cjalr	t2
	li	a1, 42
.LBB0_12:                               # Label of block must be emitted
	ct.auipcc	t2, %cheriot_compartment_hi(__library_import_libcalls__Z14griotte_assertii)
	ct.clc	t2, %cheriot_compartment_lo_i(.LBB0_12)(t2)
	ct.cjalr	t2
	li	a0, 0
	li	a1, 0
	ct.clc	ra, 8(sp)                       # 8-byte Folded Reload
	ct.clc	s0, 0(sp)                       # 8-byte Folded Reload
	ct.cincoffset	sp, sp, 16
	ct.cret
.Lfunc_end0:
	.size	_Z3runv, .Lfunc_end0-_Z3runv
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

	.type	_ZL1x,@object                   # @_ZL1x
	.section	.data._ZL1x,"aw",@progbits
	.p2align	2, 0x0
_ZL1x:
	.word	42                              # 0x2a
	.size	_ZL1x, 4

	.ident	"clang version 21.1.7 (CHERIoT-Platform/llvm-project-DLLVM_VC_REVISION=2b6c51c910ebe464ae686520aa2ba253b9e5f19e)"
	.section	".note.GNU-stack","",@progbits
	.addrsig
	.addrsig_sym __export.sealing_type.allocator.MallocKey
	.addrsig_sym __default_malloc_capability
	.addrsig_sym _ZL1x
	.section	.compartment_exports,"aR",@progbits
	.type	__export_main__Z3runv,@object
	.globl	__export_main__Z3runv
	.p2align	2, 0x0
__export_main__Z3runv:
	.half	_Z3runv-__compartment_pcc_start
	.byte	2
	.byte	8
	.size	__export_main__Z3runv, 4
	.section	.compartment_imports._Z3advv,"aG",@progbits,__import_adv__Z3advv,comdat
	.type	__import_adv__Z3advv,@object
	.weak	__import_adv__Z3advv
	.p2align	3, 0x0
__import_adv__Z3advv:
	.word	__export_adv__Z3advv
	.word	0
	.size	__import_adv__Z3advv, 8
	.section	.compartment_imports._Z10stats_readPi,"aG",@progbits,__import_stats__Z10stats_readPi,comdat
	.type	__import_stats__Z10stats_readPi,@object
	.weak	__import_stats__Z10stats_readPi
	.p2align	3, 0x0
__import_stats__Z10stats_readPi:
	.word	__export_stats__Z10stats_readPi
	.word	0
	.size	__import_stats__Z10stats_readPi, 8
	.section	.compartment_imports._Z14griotte_assertii,"aG",@progbits,__library_import_libcalls__Z14griotte_assertii,comdat
	.type	__library_import_libcalls__Z14griotte_assertii,@object
	.weak	__library_import_libcalls__Z14griotte_assertii
	.p2align	3, 0x0
__library_import_libcalls__Z14griotte_assertii:
	.word	__library_export_libcalls__Z14griotte_assertii+1
	.word	0
	.size	__library_import_libcalls__Z14griotte_assertii, 8
