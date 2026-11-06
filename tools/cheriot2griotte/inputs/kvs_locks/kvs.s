	.attribute	4, 16
	.attribute	5, "rv32e2p0_m2p0_c2p0_zmmul1p0_zca1p0_xcheri0p0_xcheriot1p0_xcheripurecap0p0"
	.file	"kvs.cc"
	.section	.text._Z11addOrUpdateU19__sealed_capabilityP5UKeyTii,"ax",@progbits
	.globl	_Z11addOrUpdateU19__sealed_capabilityP5UKeyTii # -- Begin function _Z11addOrUpdateU19__sealed_capabilityP5UKeyTii
	.p2align	1
	.type	_Z11addOrUpdateU19__sealed_capabilityP5UKeyTii,@function
_Z11addOrUpdateU19__sealed_capabilityP5UKeyTii: # @_Z11addOrUpdateU19__sealed_capabilityP5UKeyTii
# %bb.0:
	srli	a3, a1, 16
	bnez	a3, .LBB0_4
# %bb.1:
	ct.cincoffset	sp, sp, -48
	ct.csc	ra, 40(sp)                      # 8-byte Folded Spill
	ct.csc	s0, 32(sp)                      # 8-byte Folded Spill
	ct.csc	s1, 24(sp)                      # 8-byte Folded Spill
	mv	s1, a1
	ct.cmove	a1, a0
	ct.csw	a2, 8(sp)                       # 4-byte Folded Spill
.LBB0_14:                               # Label of block must be emitted
	ct.auipcc	a0, %cheriot_compartment_hi(__import.sealing_type.kvs.SUKeyT)
	ct.clc	a0, %cheriot_compartment_lo_i(.LBB0_14)(a0)
.LBB0_15:                               # Label of block must be emitted
	ct.auipcc	t2, %cheriot_compartment_hi(__library_import_libcalls__Z16token_obj_unsealP12TokenKeyTypeU19__sealed_capabilityPv)
	ct.clc	t2, %cheriot_compartment_lo_i(.LBB0_15)(t2)
	ct.cjalr	t2
	ct.clw	a0, 0(a0)
	ct.csw	a0, 12(sp)                      # 4-byte Folded Spill
.LBB0_16:                               # Label of block must be emitted
	ct.auicgp	a0, %cheriot_compartment_hi(globals)
	ct.cincoffset	a0, a0, %cheriot_compartment_lo_i(.LBB0_16)
	ct.csetbounds	a0, a0, %cheriot_compartment_size(globals)
	ct.csc	a0, 16(sp)                      # 8-byte Folded Spill
	ct.cincoffset	s0, a0, 192
.LBB0_2:                                # =>This Inner Loop Header: Depth=1
	ct.cmove	a0, s0
.LBB0_17:                               #   in Loop: Header=BB0_2 Depth=1
                                        # Label of block must be emitted
	ct.auipcc	t2, %cheriot_compartment_hi(__library_import_libcalls__Z8try_lockPi)
	ct.clc	t2, %cheriot_compartment_lo_i(.LBB0_17)(t2)
	ct.cjalr	t2
	beqz	a0, .LBB0_5
# %bb.3:                                #   in Loop: Header=BB0_2 Depth=1
	#APP
	ecall
	#NO_APP
	j	.LBB0_2
.LBB0_4:
	li	a0, -1
	j	.LBB0_13
.LBB0_5:
	ct.clw	a1, 12(sp)                      # 4-byte Folded Reload
	slli	a1, a1, 16
	ct.clc	s0, 16(sp)                      # 8-byte Folded Reload
	ct.cincoffset	a2, s0, 8
	li	a3, -1
	or	a1, a1, s1
	li	a4, 16
	beq	a0, a4, .LBB0_9
.LBB0_6:                                # =>This Inner Loop Header: Depth=1
	ct.clw	s1, -8(a2)
	mv	a5, a0
	beqz	s1, .LBB0_8
# %bb.7:                                #   in Loop: Header=BB0_6 Depth=1
	ct.clw	s1, -4(a2)
	mv	a5, a3
	beq	s1, a1, .LBB0_11
.LBB0_8:                                #   in Loop: Header=BB0_6 Depth=1
	addi	a0, a0, 1
	ct.cincoffset	a2, a2, 12
	mv	a3, a5
	bne	a0, a4, .LBB0_6
.LBB0_9:
	li	a0, -1
	beq	a3, a0, .LBB0_12
# %bb.10:
	li	a0, 0
	li	a2, 12
	mul	a2, a3, a2
	li	a3, 1
	ct.cincoffset	a2, s0, a2
	ct.csw	a3, 0(a2)
	ct.csw	a1, 4(a2)
	ct.clw	a1, 8(sp)                       # 4-byte Folded Reload
	ct.csw	a1, 8(a2)
	j	.LBB0_12
.LBB0_11:
	li	a0, 0
	ct.clw	a1, 8(sp)                       # 4-byte Folded Reload
	ct.csw	a1, 0(a2)
.LBB0_12:
	ct.csw	zero, 192(s0)
	ct.clc	ra, 40(sp)                      # 8-byte Folded Reload
	ct.clc	s0, 32(sp)                      # 8-byte Folded Reload
	ct.clc	s1, 24(sp)                      # 8-byte Folded Reload
	ct.cincoffset	sp, sp, 48
.LBB0_13:
	li	a1, 0
	ct.cret
.Lfunc_end0:
	.size	_Z11addOrUpdateU19__sealed_capabilityP5UKeyTii, .Lfunc_end0-_Z11addOrUpdateU19__sealed_capabilityP5UKeyTii
                                        # -- End function
	.section	.text._Z4readU19__sealed_capabilityP5UKeyTi,"ax",@progbits
	.globl	_Z4readU19__sealed_capabilityP5UKeyTi # -- Begin function _Z4readU19__sealed_capabilityP5UKeyTi
	.p2align	1
	.type	_Z4readU19__sealed_capabilityP5UKeyTi,@function
_Z4readU19__sealed_capabilityP5UKeyTi:  # @_Z4readU19__sealed_capabilityP5UKeyTi
# %bb.0:
	srli	a2, a1, 16
	bnez	a2, .LBB1_4
# %bb.1:
	ct.cincoffset	sp, sp, -48
	ct.csc	ra, 40(sp)                      # 8-byte Folded Spill
	ct.csc	s0, 32(sp)                      # 8-byte Folded Spill
	ct.csc	s1, 24(sp)                      # 8-byte Folded Spill
	mv	s0, a1
	ct.cmove	a1, a0
.LBB1_12:                               # Label of block must be emitted
	ct.auipcc	a0, %cheriot_compartment_hi(__import.sealing_type.kvs.SUKeyT)
	ct.clc	a0, %cheriot_compartment_lo_i(.LBB1_12)(a0)
.LBB1_13:                               # Label of block must be emitted
	ct.auipcc	t2, %cheriot_compartment_hi(__library_import_libcalls__Z16token_obj_unsealP12TokenKeyTypeU19__sealed_capabilityPv)
	ct.clc	t2, %cheriot_compartment_lo_i(.LBB1_13)(t2)
	ct.cjalr	t2
	ct.clw	a0, 0(a0)
	ct.csw	a0, 12(sp)                      # 4-byte Folded Spill
.LBB1_14:                               # Label of block must be emitted
	ct.auicgp	a0, %cheriot_compartment_hi(globals)
	ct.cincoffset	a0, a0, %cheriot_compartment_lo_i(.LBB1_14)
	ct.csetbounds	a0, a0, %cheriot_compartment_size(globals)
	ct.csc	a0, 16(sp)                      # 8-byte Folded Spill
	ct.cincoffset	s1, a0, 192
.LBB1_2:                                # =>This Inner Loop Header: Depth=1
	ct.cmove	a0, s1
.LBB1_15:                               #   in Loop: Header=BB1_2 Depth=1
                                        # Label of block must be emitted
	ct.auipcc	t2, %cheriot_compartment_hi(__library_import_libcalls__Z8try_lockPi)
	ct.clc	t2, %cheriot_compartment_lo_i(.LBB1_15)(t2)
	ct.cjalr	t2
	beqz	a0, .LBB1_5
# %bb.3:                                #   in Loop: Header=BB1_2 Depth=1
	#APP
	ecall
	#NO_APP
	j	.LBB1_2
.LBB1_4:
	li	a1, 0
	li	a0, -1
	ct.cret
.LBB1_5:
	ct.clw	a1, 12(sp)                      # 4-byte Folded Reload
	slli	a1, a1, 16
	ct.clc	a4, 16(sp)                      # 8-byte Folded Reload
	ct.cincoffset	a0, a4, 8
	or	a1, a1, s0
	li	a2, 16
	beqz	a2, .LBB1_9
.LBB1_6:                                # =>This Inner Loop Header: Depth=1
	ct.clw	a3, -8(a0)
	beqz	a3, .LBB1_8
# %bb.7:                                #   in Loop: Header=BB1_6 Depth=1
	ct.clw	a3, -4(a0)
	beq	a3, a1, .LBB1_10
.LBB1_8:                                #   in Loop: Header=BB1_6 Depth=1
	ct.cincoffset	a0, a0, 12
	addi	a2, a2, -1
	bnez	a2, .LBB1_6
.LBB1_9:
	li	a1, 0
	li	a0, -1
	j	.LBB1_11
.LBB1_10:
	ct.clw	a1, 0(a0)
	li	a0, 0
.LBB1_11:
	ct.csw	zero, 192(a4)
	ct.clc	ra, 40(sp)                      # 8-byte Folded Reload
	ct.clc	s0, 32(sp)                      # 8-byte Folded Reload
	ct.clc	s1, 24(sp)                      # 8-byte Folded Reload
	ct.cincoffset	sp, sp, 48
	ct.cret
.Lfunc_end1:
	.size	_Z4readU19__sealed_capabilityP5UKeyTi, .Lfunc_end1-_Z4readU19__sealed_capabilityP5UKeyTi
                                        # -- End function
	.section	.text._Z5eraseU19__sealed_capabilityP5UKeyTi,"ax",@progbits
	.globl	_Z5eraseU19__sealed_capabilityP5UKeyTi # -- Begin function _Z5eraseU19__sealed_capabilityP5UKeyTi
	.p2align	1
	.type	_Z5eraseU19__sealed_capabilityP5UKeyTi,@function
_Z5eraseU19__sealed_capabilityP5UKeyTi: # @_Z5eraseU19__sealed_capabilityP5UKeyTi
# %bb.0:
	srli	a2, a1, 16
	bnez	a2, .LBB2_10
# %bb.1:
	ct.cincoffset	sp, sp, -32
	ct.csc	ra, 24(sp)                      # 8-byte Folded Spill
	ct.csc	s0, 16(sp)                      # 8-byte Folded Spill
	ct.csc	s1, 8(sp)                       # 8-byte Folded Spill
	ct.cmove	a3, a0
	ct.csw	a1, 4(sp)                       # 4-byte Folded Spill
.LBB2_11:                               # Label of block must be emitted
	ct.auipcc	a0, %cheriot_compartment_hi(__import.sealing_type.kvs.SUKeyT)
	ct.clc	a0, %cheriot_compartment_lo_i(.LBB2_11)(a0)
	ct.cmove	a1, a3
.LBB2_12:                               # Label of block must be emitted
	ct.auipcc	t2, %cheriot_compartment_hi(__library_import_libcalls__Z16token_obj_unsealP12TokenKeyTypeU19__sealed_capabilityPv)
	ct.clc	t2, %cheriot_compartment_lo_i(.LBB2_12)(t2)
	ct.cjalr	t2
	ct.clw	a0, 0(a0)
	ct.csw	a0, 0(sp)                       # 4-byte Folded Spill
.LBB2_13:                               # Label of block must be emitted
	ct.auicgp	s0, %cheriot_compartment_hi(globals)
	ct.cincoffset	s0, s0, %cheriot_compartment_lo_i(.LBB2_13)
	ct.csetbounds	s0, s0, %cheriot_compartment_size(globals)
	ct.cincoffset	s1, s0, 192
.LBB2_2:                                # =>This Inner Loop Header: Depth=1
	ct.cmove	a0, s1
.LBB2_14:                               #   in Loop: Header=BB2_2 Depth=1
                                        # Label of block must be emitted
	ct.auipcc	t2, %cheriot_compartment_hi(__library_import_libcalls__Z8try_lockPi)
	ct.clc	t2, %cheriot_compartment_lo_i(.LBB2_14)(t2)
	ct.cjalr	t2
	beqz	a0, .LBB2_4
# %bb.3:                                #   in Loop: Header=BB2_2 Depth=1
	#APP
	ecall
	#NO_APP
	j	.LBB2_2
.LBB2_4:
	ct.clw	a0, 0(sp)                       # 4-byte Folded Reload
	slli	a0, a0, 16
	ct.clw	a1, 4(sp)                       # 4-byte Folded Reload
	or	a0, a0, a1
	li	a1, 16
	beqz	a1, .LBB2_9
.LBB2_5:                                # =>This Inner Loop Header: Depth=1
	ct.clw	a2, 0(s0)
	beqz	a2, .LBB2_7
# %bb.6:                                #   in Loop: Header=BB2_5 Depth=1
	ct.clw	a2, 4(s0)
	beq	a2, a0, .LBB2_8
.LBB2_7:                                #   in Loop: Header=BB2_5 Depth=1
	addi	a1, a1, -1
	ct.cincoffset	s0, s0, 12
	beqz	a1, .LBB2_9
	j	.LBB2_5
.LBB2_8:
	ct.csw	zero, 0(s0)
.LBB2_9:
.LBB2_15:                               # Label of block must be emitted
	ct.auicgp	a0, %cheriot_compartment_hi(globals)
	ct.cincoffset	a0, a0, %cheriot_compartment_lo_i(.LBB2_15)
	ct.csw	zero, 192(a0)
	ct.clc	ra, 24(sp)                      # 8-byte Folded Reload
	ct.clc	s0, 16(sp)                      # 8-byte Folded Reload
	ct.clc	s1, 8(sp)                       # 8-byte Folded Reload
	ct.cincoffset	sp, sp, 32
.LBB2_10:
	li	a0, 0
	li	a1, 0
	ct.cret
.Lfunc_end2:
	.size	_Z5eraseU19__sealed_capabilityP5UKeyTi, .Lfunc_end2-_Z5eraseU19__sealed_capabilityP5UKeyTi
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

	.type	globals,@object                 # @globals
	.section	.data.globals,"aw",@progbits
	.globl	globals
	.p2align	2, 0x0
globals:
	.word	0                               # 0x0
	.word	4294967295                      # 0xffffffff
	.word	0                               # 0x0
	.word	0                               # 0x0
	.word	4294967295                      # 0xffffffff
	.word	0                               # 0x0
	.word	0                               # 0x0
	.word	4294967295                      # 0xffffffff
	.word	0                               # 0x0
	.word	0                               # 0x0
	.word	4294967295                      # 0xffffffff
	.word	0                               # 0x0
	.word	0                               # 0x0
	.word	4294967295                      # 0xffffffff
	.word	0                               # 0x0
	.word	0                               # 0x0
	.word	4294967295                      # 0xffffffff
	.word	0                               # 0x0
	.word	0                               # 0x0
	.word	4294967295                      # 0xffffffff
	.word	0                               # 0x0
	.word	0                               # 0x0
	.word	4294967295                      # 0xffffffff
	.word	0                               # 0x0
	.word	0                               # 0x0
	.word	4294967295                      # 0xffffffff
	.word	0                               # 0x0
	.word	0                               # 0x0
	.word	4294967295                      # 0xffffffff
	.word	0                               # 0x0
	.word	0                               # 0x0
	.word	4294967295                      # 0xffffffff
	.word	0                               # 0x0
	.word	0                               # 0x0
	.word	4294967295                      # 0xffffffff
	.word	0                               # 0x0
	.word	0                               # 0x0
	.word	4294967295                      # 0xffffffff
	.word	0                               # 0x0
	.word	0                               # 0x0
	.word	4294967295                      # 0xffffffff
	.word	0                               # 0x0
	.word	0                               # 0x0
	.word	4294967295                      # 0xffffffff
	.word	0                               # 0x0
	.word	0                               # 0x0
	.word	4294967295                      # 0xffffffff
	.word	0                               # 0x0
	.word	0                               # 0x0
	.size	globals, 196

	.ident	"clang version 21.1.7 (CHERIoT-Platform/llvm-project-DLLVM_VC_REVISION=2b6c51c910ebe464ae686520aa2ba253b9e5f19e)"
	.section	".note.GNU-stack","",@progbits
	.addrsig
	.addrsig_sym __export.sealing_type.allocator.MallocKey
	.addrsig_sym __default_malloc_capability
	.addrsig_sym globals
	.addrsig_sym __import.sealing_type.kvs.SUKeyT
	.section	.compartment_exports,"aR",@progbits
	.type	__export_kvs__Z11addOrUpdateU19__sealed_capabilityP5UKeyTii,@object
	.globl	__export_kvs__Z11addOrUpdateU19__sealed_capabilityP5UKeyTii
	.p2align	2, 0x0
__export_kvs__Z11addOrUpdateU19__sealed_capabilityP5UKeyTii:
	.half	_Z11addOrUpdateU19__sealed_capabilityP5UKeyTii-__compartment_pcc_start
	.byte	6
	.byte	11
	.size	__export_kvs__Z11addOrUpdateU19__sealed_capabilityP5UKeyTii, 4
	.type	__export_kvs__Z4readU19__sealed_capabilityP5UKeyTi,@object
	.globl	__export_kvs__Z4readU19__sealed_capabilityP5UKeyTi
	.p2align	2, 0x0
__export_kvs__Z4readU19__sealed_capabilityP5UKeyTi:
	.half	_Z4readU19__sealed_capabilityP5UKeyTi-__compartment_pcc_start
	.byte	6
	.byte	10
	.size	__export_kvs__Z4readU19__sealed_capabilityP5UKeyTi, 4
	.type	__export_kvs__Z5eraseU19__sealed_capabilityP5UKeyTi,@object
	.globl	__export_kvs__Z5eraseU19__sealed_capabilityP5UKeyTi
	.p2align	2, 0x0
__export_kvs__Z5eraseU19__sealed_capabilityP5UKeyTi:
	.half	_Z5eraseU19__sealed_capabilityP5UKeyTi-__compartment_pcc_start
	.byte	4
	.byte	10
	.size	__export_kvs__Z5eraseU19__sealed_capabilityP5UKeyTi, 4
	.section	.compartment_exports.sealing_type.kvs.SUKeyT,"awG",@progbits,sealing_type.kvs.SUKeyT,comdat
	.type	__export.sealing_type.kvs.SUKeyT,@object
	.globl	__export.sealing_type.kvs.SUKeyT
	.p2align	2, 0x0
__export.sealing_type.kvs.SUKeyT:
	.half	0
	.byte	0
	.byte	32
	.size	__export.sealing_type.kvs.SUKeyT, 4
	.section	.compartment_imports.sealing_type.kvs.SUKeyT,"awG",@progbits,__import.sealing_type.kvs.SUKeyT,comdat
	.type	__import.sealing_type.kvs.SUKeyT,@object
	.globl	__import.sealing_type.kvs.SUKeyT
	.p2align	3, 0x0
__import.sealing_type.kvs.SUKeyT:
	.word	__export.sealing_type.kvs.SUKeyT
	.word	0
	.size	__import.sealing_type.kvs.SUKeyT, 8
	.section	.compartment_imports._Z16token_obj_unsealP12TokenKeyTypeU19__sealed_capabilityPv,"aG",@progbits,__library_import_libcalls__Z16token_obj_unsealP12TokenKeyTypeU19__sealed_capabilityPv,comdat
	.type	__library_import_libcalls__Z16token_obj_unsealP12TokenKeyTypeU19__sealed_capabilityPv,@object
	.weak	__library_import_libcalls__Z16token_obj_unsealP12TokenKeyTypeU19__sealed_capabilityPv
	.p2align	3, 0x0
__library_import_libcalls__Z16token_obj_unsealP12TokenKeyTypeU19__sealed_capabilityPv:
	.word	__library_export_libcalls__Z16token_obj_unsealP12TokenKeyTypeU19__sealed_capabilityPv+1
	.word	0
	.size	__library_import_libcalls__Z16token_obj_unsealP12TokenKeyTypeU19__sealed_capabilityPv, 8
	.section	.compartment_imports._Z8try_lockPi,"aG",@progbits,__library_import_libcalls__Z8try_lockPi,comdat
	.type	__library_import_libcalls__Z8try_lockPi,@object
	.weak	__library_import_libcalls__Z8try_lockPi
	.p2align	3, 0x0
__library_import_libcalls__Z8try_lockPi:
	.word	__library_export_libcalls__Z8try_lockPi+1
	.word	0
	.size	__library_import_libcalls__Z8try_lockPi, 8
