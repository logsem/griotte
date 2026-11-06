	.attribute	4, 16
	.attribute	5, "rv32e2p0_m2p0_c2p0_zmmul1p0_zca1p0_xcheri0p0_xcheriot1p0_xcheripurecap0p0"
	.file	"griotte_assert.cc"
	.section	.text._Z14griotte_assertii,"ax",@progbits
	.globl	_Z14griotte_assertii            # -- Begin function _Z14griotte_assertii
	.p2align	1
	.type	_Z14griotte_assertii,@function
_Z14griotte_assertii:                   # @_Z14griotte_assertii
# %bb.0:
	beq	a0, a1, .LBB0_2
# %bb.1:
.LBB0_3:                                # Label of block must be emitted
	ct.auipcc	a0, %cheriot_compartment_hi("__import_cheriot_shared_object_griotte_assert_flag_RW---")
	ct.clc	a0, %cheriot_compartment_lo_i(.LBB0_3)(a0)
	li	a1, 1
	ct.csw	a1, 0(a0)
.LBB0_2:
	ct.cret
.Lfunc_end0:
	.size	_Z14griotte_assertii, .Lfunc_end0-_Z14griotte_assertii
                                        # -- End function
	.ident	"clang version 21.1.7 (CHERIoT-Platform/llvm-project-DLLVM_VC_REVISION=2b6c51c910ebe464ae686520aa2ba253b9e5f19e)"
	.section	".note.GNU-stack","",@progbits
	.addrsig
	.section	.compartment_exports,"aR",@progbits
	.type	__library_export_libcalls__Z14griotte_assertii,@object
	.globl	__library_export_libcalls__Z14griotte_assertii
	.p2align	2, 0x0
__library_export_libcalls__Z14griotte_assertii:
	.half	_Z14griotte_assertii-__compartment_pcc_start
	.byte	0
	.byte	2
	.size	__library_export_libcalls__Z14griotte_assertii, 4
	.section	.compartment_imports.griotte_assert_flag,"awG",@progbits,"__import_cheriot_shared_object_griotte_assert_flag_RW---",comdat
	.type	"__import_cheriot_shared_object_griotte_assert_flag_RW---",@object
	.globl	"__import_cheriot_shared_object_griotte_assert_flag_RW---"
	.p2align	3, 0x0
"__import_cheriot_shared_object_griotte_assert_flag_RW---":
	.word	__cheriot_shared_object_griotte_assert_flag
	.word	__cheriot_shared_object_griotte_assert_flag_end-__cheriot_shared_object_griotte_assert_flag-1073741824
	.size	"__import_cheriot_shared_object_griotte_assert_flag_RW---", 8
