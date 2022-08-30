	.org $8000

loop:
	lda $7002
	sta $7000
	bra loop

	.org $fffc
	.word loop

