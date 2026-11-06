	.attribute	4, 16
	.attribute	5, "rv32e2p0_m2p0_c2p0_zmmul1p0_zca1p0_xcheri0p0_xcheriot1p0_xcheripurecap0p0"
	.file	"K.cc"
	.section	.text._Z4run1v,"ax",@progbits
	.globl	_Z4run1v                        # -- Begin function _Z4run1v
	.p2align	1
	.type	_Z4run1v,@function
_Z4run1v:                               # @_Z4run1v
# %bb.0:
	ct.cincoffset	sp, sp, -16
	ct.csc	ra, 8(sp)                       # 8-byte Folded Spill
.LBB0_1:                                # Label of block must be emitted
	ct.auicgp	a0, %cheriot_compartment_hi(b)
	ct.cincoffset	a0, a0, %cheriot_compartment_lo_i(.LBB0_1)
	ct.csetbounds	a0, a0, %cheriot_compartment_size(b)
.LBB0_3:                                # Label of block must be emitted
	ct.auipcc	t1, %cheriot_compartment_hi(__import_B__Z1fPVi)
	ct.clc	t1, %cheriot_compartment_lo_i(.LBB0_3)(t1)
.LBB0_2:                                # Label of block must be emitted
	ct.auipcc	t2, %cheriot_compartment_hi(.compartment_switcher)
	ct.clc	t2, %cheriot_compartment_lo_i(.LBB0_2)(t2)
	ct.cjalr	t2
.LBB0_4:                                # Label of block must be emitted
	ct.auicgp	a0, %cheriot_compartment_hi(flag)
	ct.cincoffset	a0, a0, %cheriot_compartment_lo_i(.LBB0_4)
	li	a1, 1
	ct.csw	a1, 0(a0)
	li	a0, 0
	li	a1, 0
	ct.clc	ra, 8(sp)                       # 8-byte Folded Reload
	ct.cincoffset	sp, sp, 16
	ct.cret
.Lfunc_end0:
	.size	_Z4run1v, .Lfunc_end0-_Z4run1v
                                        # -- End function
	.section	.text._Z4run2v,"ax",@progbits
	.globl	_Z4run2v                        # -- Begin function _Z4run2v
	.p2align	1
	.type	_Z4run2v,@function
_Z4run2v:                               # @_Z4run2v
# %bb.0:
	ct.cincoffset	sp, sp, -16
	ct.csc	ra, 8(sp)                       # 8-byte Folded Spill
.LBB1_4:                                # Label of block must be emitted
	ct.auicgp	a0, %cheriot_compartment_hi(flag)
	ct.cincoffset	a0, a0, %cheriot_compartment_lo_i(.LBB1_4)
.LBB1_1:                                # =>This Inner Loop Header: Depth=1
	ct.clw	a1, 0(a0)
	bnez	a1, .LBB1_3
# %bb.2:                                #   in Loop: Header=BB1_1 Depth=1
	#APP
	ecall
	#NO_APP
	j	.LBB1_1
.LBB1_3:
.LBB1_5:                                # Label of block must be emitted
	ct.auicgp	a0, %cheriot_compartment_hi(b)
	ct.cincoffset	a0, a0, %cheriot_compartment_lo_i(.LBB1_5)
	li	a1, 42
	ct.csw	a1, 0(a0)
	ct.clw	a0, 0(a0)
	li	a1, 42
.LBB1_6:                                # Label of block must be emitted
	ct.auipcc	t2, %cheriot_compartment_hi(__library_import_libcalls__Z14griotte_assertii)
	ct.clc	t2, %cheriot_compartment_lo_i(.LBB1_6)(t2)
	ct.cjalr	t2
	li	a0, 0
	li	a1, 0
	ct.clc	ra, 8(sp)                       # 8-byte Folded Reload
	ct.cincoffset	sp, sp, 16
	ct.cret
.Lfunc_end1:
	.size	_Z4run2v, .Lfunc_end1-_Z4run2v
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

	.type	flag,@object                    # @flag
	.section	.bss.flag,"aw",@nobits
	.globl	flag
	.p2align	2, 0x0
flag:
	.word	0                               # 0x0
	.size	flag, 4

	.ident	"clang version 21.1.7 (CHERIoT-Platform/llvm-project-DLLVM_VC_REVISION=2b6c51c910ebe464ae686520aa2ba253b9e5f19e)"
	.section	".note.GNU-stack","",@progbits
	.addrsig
	.addrsig_sym __export.sealing_type.allocator.MallocKey
	.addrsig_sym __default_malloc_capability
	.addrsig_sym b
	.addrsig_sym flag
	.section	.compartment_exports,"aR",@progbits
	.type	__export_K__Z4run1v,@object
	.globl	__export_K__Z4run1v
	.p2align	2, 0x0
__export_K__Z4run1v:
	.half	_Z4run1v-__compartment_pcc_start
	.byte	2
	.byte	8
	.size	__export_K__Z4run1v, 4
	.type	__export_K__Z4run2v,@object
	.globl	__export_K__Z4run2v
	.p2align	2, 0x0
__export_K__Z4run2v:
	.half	_Z4run2v-__compartment_pcc_start
	.byte	2
	.byte	8
	.size	__export_K__Z4run2v, 4
	.section	.compartment_imports._Z1fPVi,"aG",@progbits,__import_B__Z1fPVi,comdat
	.type	__import_B__Z1fPVi,@object
	.weak	__import_B__Z1fPVi
	.p2align	3, 0x0
__import_B__Z1fPVi:
	.word	__export_B__Z1fPVi
	.word	0
	.size	__import_B__Z1fPVi, 8
	.section	.compartment_imports._Z14griotte_assertii,"aG",@progbits,__library_import_libcalls__Z14griotte_assertii,comdat
	.type	__library_import_libcalls__Z14griotte_assertii,@object
	.weak	__library_import_libcalls__Z14griotte_assertii
	.p2align	3, 0x0
__library_import_libcalls__Z14griotte_assertii:
	.word	__library_export_libcalls__Z14griotte_assertii+1
	.word	0
	.size	__library_import_libcalls__Z14griotte_assertii, 8
