	.attribute	4, 16
	.attribute	5, "rv32e2p0_m2p0_c2p0_zmmul1p0_zca1p0_xcheri0p0_xcheriot1p0_xcheripurecap0p0"
	.file	"main.cc"
	.section	.text._Z7awkwardPU10chericcallFvvE,"ax",@progbits
	.globl	_Z7awkwardPU10chericcallFvvE    # -- Begin function _Z7awkwardPU10chericcallFvvE
	.p2align	1
	.type	_Z7awkwardPU10chericcallFvvE,@function
_Z7awkwardPU10chericcallFvvE:           # @_Z7awkwardPU10chericcallFvvE
# %bb.0:
	ct.cincoffset	sp, sp, -32
	ct.csc	ra, 24(sp)                      # 8-byte Folded Spill
	ct.csc	s0, 16(sp)                      # 8-byte Folded Spill
	ct.csc	s1, 8(sp)                       # 8-byte Folded Spill
	ct.cmove	s0, a0
.LBB0_1:                                # Label of block must be emitted
	ct.auicgp	s1, %cheriot_compartment_hi(a)
	ct.cincoffset	s1, s1, %cheriot_compartment_lo_i(.LBB0_1)
	ct.csw	zero, 0(s1)
	ct.cmove	t1, s0
.LBB0_2:                                # Label of block must be emitted
	ct.auipcc	t2, %cheriot_compartment_hi(.compartment_switcher)
	ct.clc	t2, %cheriot_compartment_lo_i(.LBB0_2)(t2)
	ct.cjalr	t2
	li	a0, 1
	ct.csw	a0, 0(s1)
	ct.cmove	t1, s0
.LBB0_3:                                # Label of block must be emitted
	ct.auipcc	t2, %cheriot_compartment_hi(.compartment_switcher)
	ct.clc	t2, %cheriot_compartment_lo_i(.LBB0_3)(t2)
	ct.cjalr	t2
	ct.clw	a0, 0(s1)
	li	a1, 1
.LBB0_4:                                # Label of block must be emitted
	ct.auipcc	t2, %cheriot_compartment_hi(__library_import_libcalls__Z14griotte_assertii)
	ct.clc	t2, %cheriot_compartment_lo_i(.LBB0_4)(t2)
	ct.cjalr	t2
	li	a0, 0
	li	a1, 0
	ct.clc	ra, 24(sp)                      # 8-byte Folded Reload
	ct.clc	s0, 16(sp)                      # 8-byte Folded Reload
	ct.clc	s1, 8(sp)                       # 8-byte Folded Reload
	ct.cincoffset	sp, sp, 32
	ct.cret
.Lfunc_end0:
	.size	_Z7awkwardPU10chericcallFvvE, .Lfunc_end0-_Z7awkwardPU10chericcallFvvE
                                        # -- End function
	.section	.text._Z5entryv,"ax",@progbits
	.globl	_Z5entryv                       # -- Begin function _Z5entryv
	.p2align	1
	.type	_Z5entryv,@function
_Z5entryv:                              # @_Z5entryv
# %bb.0:
	ct.cincoffset	sp, sp, -16
	ct.csc	ra, 8(sp)                       # 8-byte Folded Spill
.LBB1_1:                                # Label of block must be emitted
	ct.auicgp	a0, %cheriot_compartment_hi(a)
	ct.cincoffset	a0, a0, %cheriot_compartment_lo_i(.LBB1_1)
	ct.csw	zero, 0(a0)
.LBB1_3:                                # Label of block must be emitted
	ct.auipcc	t1, %cheriot_compartment_hi(__import_C__Z3advv)
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

	.type	a,@object                       # @a
	.section	.bss.a,"aw",@nobits
	.globl	a
	.p2align	2, 0x0
a:
	.word	0                               # 0x0
	.size	a, 4

	.ident	"clang version 21.1.7 (CHERIoT-Platform/llvm-project-DLLVM_VC_REVISION=2b6c51c910ebe464ae686520aa2ba253b9e5f19e)"
	.section	".note.GNU-stack","",@progbits
	.addrsig
	.addrsig_sym __export.sealing_type.allocator.MallocKey
	.addrsig_sym __default_malloc_capability
	.section	.compartment_exports,"aR",@progbits
	.type	__export_main__Z7awkwardPU10chericcallFvvE,@object
	.globl	__export_main__Z7awkwardPU10chericcallFvvE
	.p2align	2, 0x0
__export_main__Z7awkwardPU10chericcallFvvE:
	.half	_Z7awkwardPU10chericcallFvvE-__compartment_pcc_start
	.byte	4
	.byte	9
	.size	__export_main__Z7awkwardPU10chericcallFvvE, 4
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
