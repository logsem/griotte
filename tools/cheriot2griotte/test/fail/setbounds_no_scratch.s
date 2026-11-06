# Rejection test of the lowering: csetbounds without two dead scratch registers (D3)
	.section	.text._Z3runv,"ax",@progbits
	.globl	_Z3runv
_Z3runv:
.LBB0_1:
	ct.auicgp	s0, %cheriot_compartment_hi(b)
	ct.cincoffset	s0, s0, %cheriot_compartment_lo_i(.LBB0_1)
	ct.csetbounds	s0, s0, %cheriot_compartment_size(b)
	add	s1, t0, t1
	add	s1, t2, a0
	add	s1, a1, a2
	add	s1, a3, a4
	add	s1, a5, s1
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
