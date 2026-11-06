	.attribute	4, 16
	.attribute	5, "rv32e2p0_m2p0_c2p0_zmmul1p0_zca1p0_xcheri0p0_xcheriot1p0_xcheripurecap0p0"
	.file	"known.cc"
                                        # Start of file scope inline assembly
	.section	.text.setjmp,"axwG",@progbits,setjmp,comdat
	.globl	setjmp
	.p2align	2
	.type	setjmp,@function
setjmp:
	ct.csc	s0, 0(a0)
	ct.csc	s1, 8(a0)
	ct.csc	sp, 16(a0)
	ct.csc	ra, 24(a0)
	li	a0, 0
	ct.cret
	.section	.text.longjmp,"axwG",@progbits,longjmp,comdat
	.globl	longjmp
	.p2align	2
	.type	longjmp,@function
longjmp:
	ct.clc	s0, 0(a0)
	ct.clc	s1, 8(a0)
	ct.clc	sp, 16(a0)
	ct.clc	ra, 24(a0)
	mv	a0, a1
	ct.cret

                                        # End of file scope inline assembly
	.section	.text._Z3runv,"ax",@progbits
	.globl	_Z3runv                         # -- Begin function _Z3runv
	.p2align	1
	.type	_Z3runv,@function
_Z3runv:                                # @_Z3runv
# %bb.0:
	ct.cincoffset	sp, sp, -16
	ct.csc	ra, 8(sp)                       # 8-byte Folded Spill
.LBB0_1:                                # Label of block must be emitted
	ct.auicgp	a0, %cheriot_compartment_hi(pi)
	ct.cincoffset	a0, a0, %cheriot_compartment_lo_i(.LBB0_1)
	ct.csetbounds	a0, a0, %cheriot_compartment_size(pi)
	ct.cgetperm	a1, a0
	andi	a1, a1, -9
	ct.candperm	a0, a0, a1
.LBB0_3:                                # Label of block must be emitted
	ct.auipcc	t1, %cheriot_compartment_hi(__import_unknown__Z3advPPi)
	ct.clc	t1, %cheriot_compartment_lo_i(.LBB0_3)(t1)
.LBB0_2:                                # Label of block must be emitted
	ct.auipcc	t2, %cheriot_compartment_hi(.compartment_switcher)
	ct.clc	t2, %cheriot_compartment_lo_i(.LBB0_2)(t2)
	ct.cjalr	t2
.LBB0_4:                                # Label of block must be emitted
	ct.auicgp	a0, %cheriot_compartment_hi(i)
	ct.cincoffset	a0, a0, %cheriot_compartment_lo_i(.LBB0_4)
	ct.clw	a0, 0(a0)
	li	a1, 42
.LBB0_5:                                # Label of block must be emitted
	ct.auipcc	t2, %cheriot_compartment_hi(__library_import_libcalls__Z14griotte_assertii)
	ct.clc	t2, %cheriot_compartment_lo_i(.LBB0_5)(t2)
	ct.cjalr	t2
	li	a0, 0
	li	a1, 0
	ct.clc	ra, 8(sp)                       # 8-byte Folded Reload
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

	.type	i,@object                       # @i
	.section	.data.i,"aw",@progbits
	.globl	i
	.p2align	2, 0x0
i:
	.word	42                              # 0x2a
	.size	i, 4

	.type	pi,@object                      # @pi
	.section	.data.pi,"aw",@progbits
	.globl	pi
	.p2align	3, 0x0
pi:
	.chericap	i
	.size	pi, 8

	.ident	"clang version 21.1.7 (CHERIoT-Platform/llvm-project-DLLVM_VC_REVISION=2b6c51c910ebe464ae686520aa2ba253b9e5f19e)"
	.section	".note.GNU-stack","",@progbits
	.addrsig
	.addrsig_sym __export.sealing_type.allocator.MallocKey
	.addrsig_sym __default_malloc_capability
	.addrsig_sym i
	.addrsig_sym pi
	.section	.compartment_exports,"aR",@progbits
	.type	__export_known__Z3runv,@object
	.globl	__export_known__Z3runv
	.p2align	2, 0x0
__export_known__Z3runv:
	.half	_Z3runv-__compartment_pcc_start
	.byte	2
	.byte	8
	.size	__export_known__Z3runv, 4
	.section	.compartment_imports._Z3advPPi,"aG",@progbits,__import_unknown__Z3advPPi,comdat
	.type	__import_unknown__Z3advPPi,@object
	.weak	__import_unknown__Z3advPPi
	.p2align	3, 0x0
__import_unknown__Z3advPPi:
	.word	__export_unknown__Z3advPPi
	.word	0
	.size	__import_unknown__Z3advPPi, 8
	.section	.compartment_imports._Z14griotte_assertii,"aG",@progbits,__library_import_libcalls__Z14griotte_assertii,comdat
	.type	__library_import_libcalls__Z14griotte_assertii,@object
	.weak	__library_import_libcalls__Z14griotte_assertii
	.p2align	3, 0x0
__library_import_libcalls__Z14griotte_assertii:
	.word	__library_export_libcalls__Z14griotte_assertii+1
	.word	0
	.size	__library_import_libcalls__Z14griotte_assertii, 8
