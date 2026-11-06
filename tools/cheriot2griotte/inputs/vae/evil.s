	.attribute	4, 16
	.attribute	5, "rv32e2p0_m2p0_c2p0_zmmul1p0_zca1p0_xcheri0p0_xcheriot1p0_xcheripurecap0p0"
	.file	"evil.cc"
	.section	.text._Z1gv,"ax",@progbits
	.globl	_Z1gv                           # -- Begin function _Z1gv
	.p2align	1
	.type	_Z1gv,@function
_Z1gv:                                  # @_Z1gv
# %bb.0:
	ct.cincoffset	sp, sp, -16
	ct.csc	ra, 8(sp)                       # 8-byte Folded Spill
.LBB0_5:                                # Label of block must be emitted
	ct.auicgp	a1, %cheriot_compartment_hi(b)
	ct.cincoffset	a1, a1, %cheriot_compartment_lo_i(.LBB0_5)
	ct.clw	a0, 0(a1)
	addi	a2, a0, 1
	li	a3, 1
	ct.csw	a2, 0(a1)
	bne	a0, a3, .LBB0_2
# %bb.1:
.LBB0_6:                                # Label of block must be emitted
	ct.auicgp	a0, %cheriot_compartment_hi(ret)
	ct.cincoffset	a0, a0, %cheriot_compartment_lo_i(.LBB0_6)
	ct.csc	ra, 0(a0)
.LBB0_7:                                # Label of block must be emitted
	ct.auipcc	a0, %cheriot_compartment_hi(__import_evil__Z1gv)
	ct.clc	a0, %cheriot_compartment_lo_i(.LBB0_7)(a0)
.LBB0_9:                                # Label of block must be emitted
	ct.auipcc	t1, %cheriot_compartment_hi(__import_known__Z3awkPU10chericcallFvvE)
	ct.clc	t1, %cheriot_compartment_lo_i(.LBB0_9)(t1)
.LBB0_8:                                # Label of block must be emitted
	ct.auipcc	t2, %cheriot_compartment_hi(.compartment_switcher)
	ct.clc	t2, %cheriot_compartment_lo_i(.LBB0_8)(t2)
	ct.cjalr	t2
	j	.LBB0_3
.LBB0_2:
	li	a1, 2
	beq	a0, a1, .LBB0_4
.LBB0_3:
	li	a0, 0
	li	a1, 0
	ct.clc	ra, 8(sp)                       # 8-byte Folded Reload
	ct.cincoffset	sp, sp, 16
	ct.cret
.LBB0_4:
.LBB0_10:                               # Label of block must be emitted
	ct.auicgp	a0, %cheriot_compartment_hi(ret)
	ct.cincoffset	a0, a0, %cheriot_compartment_lo_i(.LBB0_10)
	ct.clc	a0, 0(a0)
	#APP
	ct.cmove	ra, a0
	ct.cret

	#NO_APP
.Lfunc_end0:
	.size	_Z1gv, .Lfunc_end0-_Z1gv
                                        # -- End function
	.section	.text._Z3advv,"ax",@progbits
	.globl	_Z3advv                         # -- Begin function _Z3advv
	.p2align	1
	.type	_Z3advv,@function
_Z3advv:                                # @_Z3advv
# %bb.0:
	ct.cincoffset	sp, sp, -16
	ct.csc	ra, 8(sp)                       # 8-byte Folded Spill
.LBB1_1:                                # Label of block must be emitted
	ct.auipcc	a0, %cheriot_compartment_hi(__import_evil__Z1gv)
	ct.clc	a0, %cheriot_compartment_lo_i(.LBB1_1)(a0)
.LBB1_3:                                # Label of block must be emitted
	ct.auipcc	t1, %cheriot_compartment_hi(__import_known__Z3awkPU10chericcallFvvE)
	ct.clc	t1, %cheriot_compartment_lo_i(.LBB1_3)(t1)
.LBB1_2:                                # Label of block must be emitted
	ct.auipcc	t2, %cheriot_compartment_hi(.compartment_switcher)
	ct.clc	t2, %cheriot_compartment_lo_i(.LBB1_2)(t2)
	ct.cjalr	t2
	li	a0, 0
	li	a1, 0
	ct.clc	ra, 8(sp)                       # 8-byte Folded Reload
	ct.cincoffset	sp, sp, 16
	ct.cret
.Lfunc_end1:
	.size	_Z3advv, .Lfunc_end1-_Z3advv
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

	.type	ret,@object                     # @ret
	.section	.bss.ret,"aw",@nobits
	.globl	ret
	.p2align	3, 0x0
ret:
	.chericap	0
	.size	ret, 8

	.ident	"clang version 21.1.7 (CHERIoT-Platform/llvm-project-DLLVM_VC_REVISION=2b6c51c910ebe464ae686520aa2ba253b9e5f19e)"
	.section	".note.GNU-stack","",@progbits
	.addrsig
	.addrsig_sym _Z1gv
	.addrsig_sym __export.sealing_type.allocator.MallocKey
	.addrsig_sym __default_malloc_capability
	.section	.compartment_exports,"aR",@progbits
	.type	__export_evil__Z1gv,@object
	.p2align	2, 0x0
__export_evil__Z1gv:
	.half	_Z1gv-__compartment_pcc_start
	.byte	0
	.byte	8
	.size	__export_evil__Z1gv, 4
	.type	__export_evil__Z3advv,@object
	.globl	__export_evil__Z3advv
	.p2align	2, 0x0
__export_evil__Z3advv:
	.half	_Z3advv-__compartment_pcc_start
	.byte	2
	.byte	8
	.size	__export_evil__Z3advv, 4
	.section	.compartment_imports._Z1gv,"aG",@progbits,__import_evil__Z1gv,comdat
	.type	__import_evil__Z1gv,@object
	.weak	__import_evil__Z1gv
	.p2align	3, 0x0
__import_evil__Z1gv:
	.word	__export_evil__Z1gv
	.word	0
	.size	__import_evil__Z1gv, 8
	.section	.compartment_imports._Z3awkPU10chericcallFvvE,"aG",@progbits,__import_known__Z3awkPU10chericcallFvvE,comdat
	.type	__import_known__Z3awkPU10chericcallFvvE,@object
	.weak	__import_known__Z3awkPU10chericcallFvvE
	.p2align	3, 0x0
__import_known__Z3awkPU10chericcallFvvE:
	.word	__export_known__Z3awkPU10chericcallFvvE
	.word	0
	.size	__import_known__Z3awkPU10chericcallFvvE, 8
