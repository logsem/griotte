	.attribute	4, 16
	.attribute	5, "rv32e2p0_m2p0_c2p0_zmmul1p0_zca1p0_xcheri0p0_xcheriot1p0_xcheripurecap0p0"
	.file	"C.cc"
	.section	.text._Z1gPVi,"ax",@progbits
	.globl	_Z1gPVi                         # -- Begin function _Z1gPVi
	.p2align	1
	.type	_Z1gPVi,@function
_Z1gPVi:                                # @_Z1gPVi
# %bb.0:
	li	a1, 9
	ct.csw	a1, 0(a0)
	li	a0, 0
	li	a1, 0
	ct.cret
.Lfunc_end0:
	.size	_Z1gPVi, .Lfunc_end0-_Z1gPVi
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
	.type	__export_C__Z1gPVi,@object
	.globl	__export_C__Z1gPVi
	.p2align	2, 0x0
__export_C__Z1gPVi:
	.half	_Z1gPVi-__compartment_pcc_start
	.byte	0
	.byte	9
	.size	__export_C__Z1gPVi, 4
