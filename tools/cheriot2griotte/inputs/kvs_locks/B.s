	.attribute	4, 16
	.attribute	5, "rv32e2p0_m2p0_c2p0_zmmul1p0_zca1p0_xcheri0p0_xcheriot1p0_xcheripurecap0p0"
	.file	"B.cc"
	.section	.text._Z1fv,"ax",@progbits
	.globl	_Z1fv                           # -- Begin function _Z1fv
	.p2align	1
	.type	_Z1fv,@function
_Z1fv:                                  # @_Z1fv
# %bb.0:
	ct.ctail	_ZL7write13v
.Lfunc_end0:
	.size	_Z1fv, .Lfunc_end0-_Z1fv
                                        # -- End function
	.section	.text._ZL7write13v,"ax",@progbits
	.p2align	1                               # -- Begin function _ZL7write13v
	.type	_ZL7write13v,@function
_ZL7write13v:                           # @_ZL7write13v
# %bb.0:
	ct.cincoffset	sp, sp, -16
	ct.csc	ra, 8(sp)                       # 8-byte Folded Spill
	#APP
	.type	__import.sealed_object.userKey,@object
	.section	.compartment_imports.userKey,"awG",@progbits,userKey
	.weak	__import.sealed_object.userKey
	.p2align	3, 0x0
__import.sealed_object.userKey:
	.word	userKey
	.word	12
	.size	__import.sealed_object.userKey, 8
	.section	.text._ZL7write13v,"ax",@progbits

.Ltmp0:
	ct.auipcc	a0, %cheriot_compartment_hi(__import.sealed_object.userKey)
	ct.clc	a0, %cheriot_compartment_lo_i(.Ltmp0)(a0)

	#NO_APP
	li	a1, 1
	li	a2, 13
.LBB1_2:                                # Label of block must be emitted
	ct.auipcc	t1, %cheriot_compartment_hi(__import_kvs__Z11addOrUpdateU19__sealed_capabilityP5UKeyTii)
	ct.clc	t1, %cheriot_compartment_lo_i(.LBB1_2)(t1)
.LBB1_1:                                # Label of block must be emitted
	ct.auipcc	t2, %cheriot_compartment_hi(.compartment_switcher)
	ct.clc	t2, %cheriot_compartment_lo_i(.LBB1_1)(t2)
	ct.cjalr	t2
	ct.clc	ra, 8(sp)                       # 8-byte Folded Reload
	ct.cincoffset	sp, sp, 16
	ct.cret
.Lfunc_end1:
	.size	_ZL7write13v, .Lfunc_end1-_ZL7write13v
                                        # -- End function
	.section	.text._Z3advv,"ax",@progbits
	.globl	_Z3advv                         # -- Begin function _Z3advv
	.p2align	1
	.type	_Z3advv,@function
_Z3advv:                                # @_Z3advv
# %bb.0:
	ct.ctail	_ZL7write13v
.Lfunc_end2:
	.size	_Z3advv, .Lfunc_end2-_Z3advv
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

	.type	userKey,@object                 # @userKey
	.section	.sealed_objects,"awG",@progbits,userKey,comdat
	.weak	userKey
	.p2align	3, 0x0
userKey:
	.word	__export.sealing_type.kvs.SUKeyT
	.word	0                               # 0x0
	.word	2                               # 0x2
	.size	userKey, 12

	.ident	"clang version 21.1.7 (CHERIoT-Platform/llvm-project-DLLVM_VC_REVISION=2b6c51c910ebe464ae686520aa2ba253b9e5f19e)"
	.section	".note.GNU-stack","",@progbits
	.addrsig
	.addrsig_sym __export.sealing_type.allocator.MallocKey
	.addrsig_sym __default_malloc_capability
	.addrsig_sym __export.sealing_type.kvs.SUKeyT
	.addrsig_sym userKey
	.section	.compartment_exports,"aR",@progbits
	.type	__export_B__Z1fv,@object
	.globl	__export_B__Z1fv
	.p2align	2, 0x0
__export_B__Z1fv:
	.half	_Z1fv-__compartment_pcc_start
	.byte	0
	.byte	8
	.size	__export_B__Z1fv, 4
	.type	__export_B__Z3advv,@object
	.globl	__export_B__Z3advv
	.p2align	2, 0x0
__export_B__Z3advv:
	.half	_Z3advv-__compartment_pcc_start
	.byte	0
	.byte	8
	.size	__export_B__Z3advv, 4
	.section	.compartment_imports._Z11addOrUpdateU19__sealed_capabilityP5UKeyTii,"aG",@progbits,__import_kvs__Z11addOrUpdateU19__sealed_capabilityP5UKeyTii,comdat
	.type	__import_kvs__Z11addOrUpdateU19__sealed_capabilityP5UKeyTii,@object
	.weak	__import_kvs__Z11addOrUpdateU19__sealed_capabilityP5UKeyTii
	.p2align	3, 0x0
__import_kvs__Z11addOrUpdateU19__sealed_capabilityP5UKeyTii:
	.word	__export_kvs__Z11addOrUpdateU19__sealed_capabilityP5UKeyTii
	.word	0
	.size	__import_kvs__Z11addOrUpdateU19__sealed_capabilityP5UKeyTii, 8
