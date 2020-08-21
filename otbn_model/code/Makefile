verify:
	dafny /compile:0 examples.dfy

examples.dfy: examples.vad decls.dfy
	vale.exe -dafnyText -in examples.vad -out examples.dfy

decls.dfy:
	vale.exe -dafnyText -in decls.vad -out decls.dfy
