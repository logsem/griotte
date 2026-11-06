	.attribute	4, 16
	.attribute	5, "rv32e2p0_m2p0_c2p0_zmmul1p0_zca1p0_xcheri0p0_xcheriot1p0_xcheripurecap0p0"
	.file	"client.cc"
	.section	.text._Z5entryv,"ax",@progbits
	.globl	_Z5entryv                       # -- Begin function _Z5entryv
	.p2align	1
	.type	_Z5entryv,@function
_Z5entryv:                              # @_Z5entryv
# %bb.0:
	ct.cincoffset	sp, sp, -48
	ct.csc	ra, 40(sp)                      # 8-byte Folded Spill
	ct.csc	s0, 32(sp)                      # 8-byte Folded Spill
	ct.csc	s1, 24(sp)                      # 8-byte Folded Spill
	ct.csw	zero, 16(sp)
	li	a0, 30
	ct.csw	a0, 20(sp)
	#APP
	.type	__import.sealed_object.__default_malloc_capability,@object
	.section	.compartment_imports.__default_malloc_capability,"awG",@progbits,__default_malloc_capability
	.weak	__import.sealed_object.__default_malloc_capability
	.p2align	3, 0x0
__import.sealed_object.__default_malloc_capability:
	.word	__default_malloc_capability
	.word	32
	.size	__import.sealed_object.__default_malloc_capability, 8
	.section	.text._Z5entryv,"ax",@progbits

.Ltmp0:
	ct.auipcc	a1, %cheriot_compartment_hi(__import.sealed_object.__default_malloc_capability)
	ct.clc	a1, %cheriot_compartment_lo_i(.Ltmp0)(a1)

	#NO_APP
	ct.csc	a1, 8(sp)                       # 8-byte Folded Spill
	ct.cincoffset	a0, sp, 16
	ct.csetbounds	a0, a0, 8
	li	a2, 1
	li	a3, 1
.LBB0_2:                                # Label of block must be emitted
	ct.auipcc	t1, %cheriot_compartment_hi(__import_allocator__Z13heap_allocate17__TimeoutArgumentU19__sealed_capabilityP24AllocatorCapabilityStatejj)
	ct.clc	t1, %cheriot_compartment_lo_i(.LBB0_2)(t1)
.LBB0_1:                                # Label of block must be emitted
	ct.auipcc	t2, %cheriot_compartment_hi(.compartment_switcher)
	ct.clc	t2, %cheriot_compartment_lo_i(.LBB0_1)(t2)
	ct.cjalr	t2
	ct.cmove	s1, a0
.LBB0_3:                                # Label of block must be emitted
	ct.auicgp	s0, %cheriot_compartment_hi(p)
	ct.cincoffset	s0, s0, %cheriot_compartment_lo_i(.LBB0_3)
	ct.csc	s0, 0(a0)
.LBB0_5:                                # Label of block must be emitted
	ct.auipcc	t1, %cheriot_compartment_hi(__import_adv__Z3advPPi)
	ct.clc	t1, %cheriot_compartment_lo_i(.LBB0_5)(t1)
.LBB0_4:                                # Label of block must be emitted
	ct.auipcc	t2, %cheriot_compartment_hi(.compartment_switcher)
	ct.clc	t2, %cheriot_compartment_lo_i(.LBB0_4)(t2)
	ct.cjalr	t2
	li	a0, 43
	ct.csw	a0, 0(s0)
	ct.clc	a0, 8(sp)                       # 8-byte Folded Reload
	ct.cmove	a1, s1
.LBB0_7:                                # Label of block must be emitted
	ct.auipcc	t1, %cheriot_compartment_hi(__import_allocator__Z9heap_freeU19__sealed_capabilityP24AllocatorCapabilityStatePv)
	ct.clc	t1, %cheriot_compartment_lo_i(.LBB0_7)(t1)
.LBB0_6:                                # Label of block must be emitted
	ct.auipcc	t2, %cheriot_compartment_hi(.compartment_switcher)
	ct.clc	t2, %cheriot_compartment_lo_i(.LBB0_6)(t2)
	ct.cjalr	t2
	ct.cmove	a0, zero
.LBB0_9:                                # Label of block must be emitted
	ct.auipcc	t1, %cheriot_compartment_hi(__import_adv__Z3advPPi)
	ct.clc	t1, %cheriot_compartment_lo_i(.LBB0_9)(t1)
.LBB0_8:                                # Label of block must be emitted
	ct.auipcc	t2, %cheriot_compartment_hi(.compartment_switcher)
	ct.clc	t2, %cheriot_compartment_lo_i(.LBB0_8)(t2)
	ct.cjalr	t2
	ct.clw	a0, 0(s0)
	li	a1, 43
.LBB0_10:                               # Label of block must be emitted
	ct.auipcc	t2, %cheriot_compartment_hi(__library_import_libcalls__Z14griotte_assertii)
	ct.clc	t2, %cheriot_compartment_lo_i(.LBB0_10)(t2)
	ct.cjalr	t2
	li	a0, 0
	li	a1, 0
	ct.clc	ra, 40(sp)                      # 8-byte Folded Reload
	ct.clc	s0, 32(sp)                      # 8-byte Folded Reload
	ct.clc	s1, 24(sp)                      # 8-byte Folded Reload
	ct.cincoffset	sp, sp, 48
	ct.cret
.Lfunc_end0:
	.size	_Z5entryv, .Lfunc_end0-_Z5entryv
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

	.type	p,@object                       # @p
	.section	.data.p,"aw",@progbits
	.globl	p
	.p2align	2, 0x0
p:
	.word	42                              # 0x2a
	.size	p, 4

	.ident	"clang version 21.1.7 (CHERIoT-Platform/llvm-project-DLLVM_VC_REVISION=2b6c51c910ebe464ae686520aa2ba253b9e5f19e)"
	.section	".note.GNU-stack","",@progbits
	.addrsig
	.addrsig_sym __export.sealing_type.allocator.MallocKey
	.addrsig_sym __default_malloc_capability
	.addrsig_sym p
	.section	.compartment_exports,"aR",@progbits
	.type	__export_client__Z5entryv,@object
	.globl	__export_client__Z5entryv
	.p2align	2, 0x0
__export_client__Z5entryv:
	.half	_Z5entryv-__compartment_pcc_start
	.byte	6
	.byte	8
	.size	__export_client__Z5entryv, 4
	.section	.compartment_imports._Z13heap_allocate17__TimeoutArgumentU19__sealed_capabilityP24AllocatorCapabilityStatejj,"aG",@progbits,__import_allocator__Z13heap_allocate17__TimeoutArgumentU19__sealed_capabilityP24AllocatorCapabilityStatejj,comdat
	.type	__import_allocator__Z13heap_allocate17__TimeoutArgumentU19__sealed_capabilityP24AllocatorCapabilityStatejj,@object
	.weak	__import_allocator__Z13heap_allocate17__TimeoutArgumentU19__sealed_capabilityP24AllocatorCapabilityStatejj
	.p2align	3, 0x0
__import_allocator__Z13heap_allocate17__TimeoutArgumentU19__sealed_capabilityP24AllocatorCapabilityStatejj:
	.word	__export_allocator__Z13heap_allocate17__TimeoutArgumentU19__sealed_capabilityP24AllocatorCapabilityStatejj
	.word	0
	.size	__import_allocator__Z13heap_allocate17__TimeoutArgumentU19__sealed_capabilityP24AllocatorCapabilityStatejj, 8
	.section	.compartment_imports._Z3advPPi,"aG",@progbits,__import_adv__Z3advPPi,comdat
	.type	__import_adv__Z3advPPi,@object
	.weak	__import_adv__Z3advPPi
	.p2align	3, 0x0
__import_adv__Z3advPPi:
	.word	__export_adv__Z3advPPi
	.word	0
	.size	__import_adv__Z3advPPi, 8
	.section	.compartment_imports._Z9heap_freeU19__sealed_capabilityP24AllocatorCapabilityStatePv,"aG",@progbits,__import_allocator__Z9heap_freeU19__sealed_capabilityP24AllocatorCapabilityStatePv,comdat
	.type	__import_allocator__Z9heap_freeU19__sealed_capabilityP24AllocatorCapabilityStatePv,@object
	.weak	__import_allocator__Z9heap_freeU19__sealed_capabilityP24AllocatorCapabilityStatePv
	.p2align	3, 0x0
__import_allocator__Z9heap_freeU19__sealed_capabilityP24AllocatorCapabilityStatePv:
	.word	__export_allocator__Z9heap_freeU19__sealed_capabilityP24AllocatorCapabilityStatePv
	.word	0
	.size	__import_allocator__Z9heap_freeU19__sealed_capabilityP24AllocatorCapabilityStatePv, 8
	.section	.compartment_imports._Z14griotte_assertii,"aG",@progbits,__library_import_libcalls__Z14griotte_assertii,comdat
	.type	__library_import_libcalls__Z14griotte_assertii,@object
	.weak	__library_import_libcalls__Z14griotte_assertii
	.p2align	3, 0x0
__library_import_libcalls__Z14griotte_assertii:
	.word	__library_export_libcalls__Z14griotte_assertii+1
	.word	0
	.size	__library_import_libcalls__Z14griotte_assertii, 8
