	.attribute	4, 16
	.attribute	5, "rv32e2p0_m2p0_c2p0_zmmul1p0_zca1p0_xcheri0p0_xcheriot1p0_xcheripurecap0p0"
	.file	"main.cc"
	.section	.text._Z5entryv,"ax",@progbits
	.globl	_Z5entryv                       # -- Begin function _Z5entryv
	.p2align	1
	.type	_Z5entryv,@function
_Z5entryv:                              # @_Z5entryv
# %bb.0:
	ct.cincoffset	sp, sp, -16
	ct.csc	ra, 8(sp)                       # 8-byte Folded Spill
	ct.csc	s0, 0(sp)                       # 8-byte Folded Spill
	#APP
	.type	__import.sealed_object.userKey,@object
	.section	.compartment_imports.userKey,"awG",@progbits,userKey
	.weak	__import.sealed_object.userKey
	.p2align	3, 0x0
__import.sealed_object.userKey:
	.word	userKey
	.word	12
	.size	__import.sealed_object.userKey, 8
	.section	.text._Z5entryv,"ax",@progbits

.Ltmp0:
	ct.auipcc	s0, %cheriot_compartment_hi(__import.sealed_object.userKey)
	ct.clc	s0, %cheriot_compartment_lo_i(.Ltmp0)(s0)

	#NO_APP
	li	a1, 1
	li	a2, 12
	ct.cmove	a0, s0
.LBB0_5:                                # Label of block must be emitted
	ct.auipcc	t1, %cheriot_compartment_hi(__import_kvs__Z11addOrUpdateU19__sealed_capabilityP5UKeyTii)
	ct.clc	t1, %cheriot_compartment_lo_i(.LBB0_5)(t1)
.LBB0_4:                                # Label of block must be emitted
	ct.auipcc	t2, %cheriot_compartment_hi(.compartment_switcher)
	ct.clc	t2, %cheriot_compartment_lo_i(.LBB0_4)(t2)
	ct.cjalr	t2
	bnez	a0, .LBB0_3
# %bb.1:
.LBB0_7:                                # Label of block must be emitted
	ct.auipcc	t1, %cheriot_compartment_hi(__import_B__Z1fv)
	ct.clc	t1, %cheriot_compartment_lo_i(.LBB0_7)(t1)
.LBB0_6:                                # Label of block must be emitted
	ct.auipcc	t2, %cheriot_compartment_hi(.compartment_switcher)
	ct.clc	t2, %cheriot_compartment_lo_i(.LBB0_6)(t2)
	ct.cjalr	t2
	li	a1, 1
	ct.cmove	a0, s0
.LBB0_9:                                # Label of block must be emitted
	ct.auipcc	t1, %cheriot_compartment_hi(__import_kvs__Z4readU19__sealed_capabilityP5UKeyTi)
	ct.clc	t1, %cheriot_compartment_lo_i(.LBB0_9)(t1)
.LBB0_8:                                # Label of block must be emitted
	ct.auipcc	t2, %cheriot_compartment_hi(.compartment_switcher)
	ct.clc	t2, %cheriot_compartment_lo_i(.LBB0_8)(t2)
	ct.cjalr	t2
	bnez	a0, .LBB0_3
# %bb.2:
	mv	a2, a1
	li	a1, 12
	mv	a0, a2
.LBB0_10:                               # Label of block must be emitted
	ct.auipcc	t2, %cheriot_compartment_hi(__library_import_libcalls__Z14griotte_assertii)
	ct.clc	t2, %cheriot_compartment_lo_i(.LBB0_10)(t2)
	ct.cjalr	t2
.LBB0_3:
	li	a0, 0
	li	a1, 0
	ct.clc	ra, 8(sp)                       # 8-byte Folded Reload
	ct.clc	s0, 0(sp)                       # 8-byte Folded Reload
	ct.cincoffset	sp, sp, 16
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

	.type	userKey,@object                 # @userKey
	.section	.sealed_objects,"awG",@progbits,userKey,comdat
	.weak	userKey
	.p2align	3, 0x0
userKey:
	.word	__export.sealing_type.kvs.SUKeyT
	.word	0                               # 0x0
	.word	1                               # 0x1
	.size	userKey, 12

	.ident	"clang version 21.1.7 (CHERIoT-Platform/llvm-project-DLLVM_VC_REVISION=2b6c51c910ebe464ae686520aa2ba253b9e5f19e)"
	.section	".note.GNU-stack","",@progbits
	.addrsig
	.addrsig_sym __export.sealing_type.allocator.MallocKey
	.addrsig_sym __default_malloc_capability
	.addrsig_sym __export.sealing_type.kvs.SUKeyT
	.addrsig_sym userKey
	.section	.compartment_exports,"aR",@progbits
	.type	__export_main__Z5entryv,@object
	.globl	__export_main__Z5entryv
	.p2align	2, 0x0
__export_main__Z5entryv:
	.half	_Z5entryv-__compartment_pcc_start
	.byte	2
	.byte	8
	.size	__export_main__Z5entryv, 4
	.section	.compartment_imports._Z11addOrUpdateU19__sealed_capabilityP5UKeyTii,"aG",@progbits,__import_kvs__Z11addOrUpdateU19__sealed_capabilityP5UKeyTii,comdat
	.type	__import_kvs__Z11addOrUpdateU19__sealed_capabilityP5UKeyTii,@object
	.weak	__import_kvs__Z11addOrUpdateU19__sealed_capabilityP5UKeyTii
	.p2align	3, 0x0
__import_kvs__Z11addOrUpdateU19__sealed_capabilityP5UKeyTii:
	.word	__export_kvs__Z11addOrUpdateU19__sealed_capabilityP5UKeyTii
	.word	0
	.size	__import_kvs__Z11addOrUpdateU19__sealed_capabilityP5UKeyTii, 8
	.section	.compartment_imports._Z1fv,"aG",@progbits,__import_B__Z1fv,comdat
	.type	__import_B__Z1fv,@object
	.weak	__import_B__Z1fv
	.p2align	3, 0x0
__import_B__Z1fv:
	.word	__export_B__Z1fv
	.word	0
	.size	__import_B__Z1fv, 8
	.section	.compartment_imports._Z4readU19__sealed_capabilityP5UKeyTi,"aG",@progbits,__import_kvs__Z4readU19__sealed_capabilityP5UKeyTi,comdat
	.type	__import_kvs__Z4readU19__sealed_capabilityP5UKeyTi,@object
	.weak	__import_kvs__Z4readU19__sealed_capabilityP5UKeyTi
	.p2align	3, 0x0
__import_kvs__Z4readU19__sealed_capabilityP5UKeyTi:
	.word	__export_kvs__Z4readU19__sealed_capabilityP5UKeyTi
	.word	0
	.size	__import_kvs__Z4readU19__sealed_capabilityP5UKeyTi, 8
	.section	.compartment_imports._Z14griotte_assertii,"aG",@progbits,__library_import_libcalls__Z14griotte_assertii,comdat
	.type	__library_import_libcalls__Z14griotte_assertii,@object
	.weak	__library_import_libcalls__Z14griotte_assertii
	.p2align	3, 0x0
__library_import_libcalls__Z14griotte_assertii:
	.word	__library_export_libcalls__Z14griotte_assertii+1
	.word	0
	.size	__library_import_libcalls__Z14griotte_assertii, 8
