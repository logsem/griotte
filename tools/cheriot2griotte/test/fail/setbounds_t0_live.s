# Rejection test of the lowering: t0 may carry an argument to a call, so it is no scratch register before one (D34)
	.section	.text._Z3runv,"ax",@progbits
	.globl	_Z3runv
_Z3runv:
.LBB0_1:
	ct.auicgp	s0, %cheriot_compartment_hi(b)
	ct.cincoffset	s0, s0, %cheriot_compartment_lo_i(.LBB0_1)
	ct.csetbounds	s0, s0, %cheriot_compartment_size(b)
.LBB0_2:
	ct.auipcc	t2, %cheriot_compartment_hi(__library_import_libcalls__Z1gv)
	ct.clc	t2, %cheriot_compartment_lo_i(.LBB0_2)(t2)
	ct.cjalr	t2
	ct.cret
.Lfunc_end0:
	.size	_Z3runv, .Lfunc_end0-_Z3runv
	.section	.bss.b,"aw",@nobits
	.globl	b
b:
	.word	0
	.size	b, 4

	.section	.compartment_exports,"aR",@progbits
	.globl	__export_main__Z3runv
__export_main__Z3runv:
	.half	_Z3runv-__compartment_pcc_start
	.byte	0
	.byte	8
	.size	__export_main__Z3runv, 4
	.section	.compartment_imports._Z1gv,"aG",@progbits,__library_import_libcalls__Z1gv,comdat
	.weak	__library_import_libcalls__Z1gv
__library_import_libcalls__Z1gv:
	.word	__library_export_libcalls__Z1gv+1
	.word	0
	.size	__library_import_libcalls__Z1gv, 8
