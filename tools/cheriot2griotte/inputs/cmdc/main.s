	.attribute	4, 16
	.attribute	5, "rv32e2p0_m2p0_c2p0_zmmul1p0_zca1p0_xcheri0p0_xcheriot1p0_xcheripurecap0p0"
	.file	"main.cc"
	.section	.text._Z3runv,"ax",@progbits
	.globl	_Z3runv                         # -- Begin function _Z3runv
	.p2align	1
	.type	_Z3runv,@function
_Z3runv:                                # @_Z3runv
# %bb.0:
	ct.cincoffset	sp, sp, -32
	ct.csc	ra, 24(sp)                      # 8-byte Folded Spill
	ct.csc	s0, 16(sp)                      # 8-byte Folded Spill
	ct.csc	s1, 8(sp)                       # 8-byte Folded Spill
.LBB0_1:                                # Label of block must be emitted
	ct.auicgp	s0, %cheriot_compartment_hi(b)
	ct.cincoffset	s0, s0, %cheriot_compartment_lo_i(.LBB0_1)
	ct.csetbounds	s0, s0, %cheriot_compartment_size(b)
.LBB0_2:                                # Label of block must be emitted
	ct.auicgp	s1, %cheriot_compartment_hi(c)
	ct.cincoffset	s1, s1, %cheriot_compartment_lo_i(.LBB0_2)
	ct.csetbounds	s1, s1, %cheriot_compartment_size(c)
	ct.csw	zero, 0(s0)
	ct.csw	zero, 0(s1)
	ct.cmove	a0, s0
.LBB0_4:                                # Label of block must be emitted
	ct.auipcc	t1, %cheriot_compartment_hi(__import_B__Z1fPi)
	ct.clc	t1, %cheriot_compartment_lo_i(.LBB0_4)(t1)
.LBB0_3:                                # Label of block must be emitted
	ct.auipcc	t2, %cheriot_compartment_hi(.compartment_switcher)
	ct.clc	t2, %cheriot_compartment_lo_i(.LBB0_3)(t2)
	ct.cjalr	t2
	ct.clw	a0, 0(s1)
	li	a1, 0
.LBB0_5:                                # Label of block must be emitted
	ct.auipcc	t2, %cheriot_compartment_hi(__library_import_libcalls__Z14griotte_assertii)
	ct.clc	t2, %cheriot_compartment_lo_i(.LBB0_5)(t2)
	ct.cjalr	t2
	li	a0, 42
	ct.csw	a0, 0(s0)
	ct.cmove	a0, s1
.LBB0_7:                                # Label of block must be emitted
	ct.auipcc	t1, %cheriot_compartment_hi(__import_C__Z1gPi)
	ct.clc	t1, %cheriot_compartment_lo_i(.LBB0_7)(t1)
.LBB0_6:                                # Label of block must be emitted
	ct.auipcc	t2, %cheriot_compartment_hi(.compartment_switcher)
	ct.clc	t2, %cheriot_compartment_lo_i(.LBB0_6)(t2)
	ct.cjalr	t2
	ct.clw	a0, 0(s0)
	li	a1, 42
.LBB0_8:                                # Label of block must be emitted
	ct.auipcc	t2, %cheriot_compartment_hi(__library_import_libcalls__Z14griotte_assertii)
	ct.clc	t2, %cheriot_compartment_lo_i(.LBB0_8)(t2)
	ct.cjalr	t2
	li	a0, 0
	li	a1, 0
	ct.clc	ra, 24(sp)                      # 8-byte Folded Reload
	ct.clc	s0, 16(sp)                      # 8-byte Folded Reload
	ct.clc	s1, 8(sp)                       # 8-byte Folded Reload
	ct.cincoffset	sp, sp, 32
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

	.type	b,@object                       # @b
	.section	.bss.b,"aw",@nobits
	.globl	b
	.p2align	2, 0x0
b:
	.word	0                               # 0x0
	.size	b, 4

	.type	c,@object                       # @c
	.section	.bss.c,"aw",@nobits
	.globl	c
	.p2align	2, 0x0
c:
	.word	0                               # 0x0
	.size	c, 4

	.ident	"clang version 21.1.7 (CHERIoT-Platform/llvm-project-DLLVM_VC_REVISION=2b6c51c910ebe464ae686520aa2ba253b9e5f19e)"
	.section	".note.GNU-stack","",@progbits
	.addrsig
	.addrsig_sym __export.sealing_type.allocator.MallocKey
	.addrsig_sym __default_malloc_capability
	.addrsig_sym b
	.addrsig_sym c
	.section	.compartment_exports,"aR",@progbits
	.type	__export_main__Z3runv,@object
	.globl	__export_main__Z3runv
	.p2align	2, 0x0
__export_main__Z3runv:
	.half	_Z3runv-__compartment_pcc_start
	.byte	4
	.byte	8
	.size	__export_main__Z3runv, 4
	.section	.compartment_imports._Z1fPi,"aG",@progbits,__import_B__Z1fPi,comdat
	.type	__import_B__Z1fPi,@object
	.weak	__import_B__Z1fPi
	.p2align	3, 0x0
__import_B__Z1fPi:
	.word	__export_B__Z1fPi
	.word	0
	.size	__import_B__Z1fPi, 8
	.section	.compartment_imports._Z14griotte_assertii,"aG",@progbits,__library_import_libcalls__Z14griotte_assertii,comdat
	.type	__library_import_libcalls__Z14griotte_assertii,@object
	.weak	__library_import_libcalls__Z14griotte_assertii
	.p2align	3, 0x0
__library_import_libcalls__Z14griotte_assertii:
	.word	__library_export_libcalls__Z14griotte_assertii+1
	.word	0
	.size	__library_import_libcalls__Z14griotte_assertii, 8
	.section	.compartment_imports._Z1gPi,"aG",@progbits,__import_C__Z1gPi,comdat
	.type	__import_C__Z1gPi,@object
	.weak	__import_C__Z1gPi
	.p2align	3, 0x0
__import_C__Z1gPi:
	.word	__export_C__Z1gPi
	.word	0
	.size	__import_C__Z1gPi, 8
