	.org $8000

reset:
	ldx #0
loop:
	lda $0,x
	sta $7000
	inx
	txa
	bne loop
	stp

	.org $fffc
	.word reset

