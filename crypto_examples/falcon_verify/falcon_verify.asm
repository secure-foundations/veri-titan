falcon_verify.elf:     file format elf32-littleriscv


Disassembly of section .text:

00010074 <main>:
   10074:	ffffd2b7          	lui	t0,0xffffd
   10078:	ffffd537          	lui	a0,0xffffd
   1007c:	000047b7          	lui	a5,0x4
   10080:	81010113          	addi	sp,sp,-2032
   10084:	fe028293          	addi	t0,t0,-32 # ffffcfe0 <__BSS_END__+0xfffe53dc>
   10088:	80050513          	addi	a0,a0,-2048 # ffffc800 <__BSS_END__+0xfffe4bfc>
   1008c:	80078793          	addi	a5,a5,-2048 # 3800 <main-0xc874>
   10090:	00a787b3          	add	a5,a5,a0
   10094:	7e112623          	sw	ra,2028(sp)
   10098:	00510133          	add	sp,sp,t0
   1009c:	00278533          	add	a0,a5,sp
   100a0:	628000ef          	jal	ra,106c8 <PQCLEAN_FALCON512_CLEAN_verify_raw.constprop.0>
   100a4:	00100793          	li	a5,1
   100a8:	02f50663          	beq	a0,a5,100d4 <main+0x60>
   100ac:	00014537          	lui	a0,0x14
   100b0:	b3c50513          	addi	a0,a0,-1220 # 13b3c <__errno+0xc>
   100b4:	149000ef          	jal	ra,109fc <puts>
   100b8:	000032b7          	lui	t0,0x3
   100bc:	02028293          	addi	t0,t0,32 # 3020 <main-0xd054>
   100c0:	00510133          	add	sp,sp,t0
   100c4:	7ec12083          	lw	ra,2028(sp)
   100c8:	00000513          	li	a0,0
   100cc:	7f010113          	addi	sp,sp,2032
   100d0:	00008067          	ret
   100d4:	00014537          	lui	a0,0x14
   100d8:	b3850513          	addi	a0,a0,-1224 # 13b38 <__errno+0x8>
   100dc:	121000ef          	jal	ra,109fc <puts>
   100e0:	fd9ff06f          	j	100b8 <main+0x44>

000100e4 <register_fini>:
   100e4:	00000793          	li	a5,0
   100e8:	00078863          	beqz	a5,100f8 <register_fini+0x14>
   100ec:	00001517          	auipc	a0,0x1
   100f0:	e6c50513          	addi	a0,a0,-404 # 10f58 <__libc_fini_array>
   100f4:	2c10006f          	j	10bb4 <atexit>
   100f8:	00008067          	ret

000100fc <_start>:
   100fc:	00008197          	auipc	gp,0x8
   10100:	a6c18193          	addi	gp,gp,-1428 # 17b68 <__global_pointer$>
   10104:	04418513          	addi	a0,gp,68 # 17bac <__malloc_max_total_mem>
   10108:	09c18613          	addi	a2,gp,156 # 17c04 <__BSS_END__>
   1010c:	40a60633          	sub	a2,a2,a0
   10110:	00000593          	li	a1,0
   10114:	740000ef          	jal	ra,10854 <memset>
   10118:	00001517          	auipc	a0,0x1
   1011c:	a9c50513          	addi	a0,a0,-1380 # 10bb4 <atexit>
   10120:	00050863          	beqz	a0,10130 <_start+0x34>
   10124:	00001517          	auipc	a0,0x1
   10128:	e3450513          	addi	a0,a0,-460 # 10f58 <__libc_fini_array>
   1012c:	289000ef          	jal	ra,10bb4 <atexit>
   10130:	690000ef          	jal	ra,107c0 <__libc_init_array>
   10134:	00012503          	lw	a0,0(sp)
   10138:	00410593          	addi	a1,sp,4
   1013c:	00000613          	li	a2,0
   10140:	f35ff0ef          	jal	ra,10074 <main>
   10144:	64c0006f          	j	10790 <exit>

00010148 <__do_global_dtors_aux>:
   10148:	ff010113          	addi	sp,sp,-16
   1014c:	00812423          	sw	s0,8(sp)
   10150:	05818413          	addi	s0,gp,88 # 17bc0 <completed.1>
   10154:	00044783          	lbu	a5,0(s0)
   10158:	00112623          	sw	ra,12(sp)
   1015c:	02079263          	bnez	a5,10180 <__do_global_dtors_aux+0x38>
   10160:	00000793          	li	a5,0
   10164:	00078a63          	beqz	a5,10178 <__do_global_dtors_aux+0x30>
   10168:	00007517          	auipc	a0,0x7
   1016c:	1ec50513          	addi	a0,a0,492 # 17354 <__FRAME_END__>
   10170:	00000097          	auipc	ra,0x0
   10174:	000000e7          	jalr	zero # 0 <main-0x10074>
   10178:	00100793          	li	a5,1
   1017c:	00f40023          	sb	a5,0(s0)
   10180:	00c12083          	lw	ra,12(sp)
   10184:	00812403          	lw	s0,8(sp)
   10188:	01010113          	addi	sp,sp,16
   1018c:	00008067          	ret

00010190 <frame_dummy>:
   10190:	00000793          	li	a5,0
   10194:	00078c63          	beqz	a5,101ac <frame_dummy+0x1c>
   10198:	05c18593          	addi	a1,gp,92 # 17bc4 <object.0>
   1019c:	00007517          	auipc	a0,0x7
   101a0:	1b850513          	addi	a0,a0,440 # 17354 <__FRAME_END__>
   101a4:	00000317          	auipc	t1,0x0
   101a8:	00000067          	jr	zero # 0 <main-0x10074>
   101ac:	00008067          	ret

000101b0 <mq_add>:
   101b0:	ffffd7b7          	lui	a5,0xffffd
   101b4:	fff78793          	addi	a5,a5,-1 # ffffcfff <__BSS_END__+0xfffe53fb>
   101b8:	00f585b3          	add	a1,a1,a5
   101bc:	00a585b3          	add	a1,a1,a0
   101c0:	000037b7          	lui	a5,0x3
   101c4:	41f5d513          	srai	a0,a1,0x1f
   101c8:	00178793          	addi	a5,a5,1 # 3001 <main-0xd073>
   101cc:	00f57533          	and	a0,a0,a5
   101d0:	00b50533          	add	a0,a0,a1
   101d4:	00008067          	ret

000101d8 <mq_sub>:
   101d8:	40b505b3          	sub	a1,a0,a1
   101dc:	000037b7          	lui	a5,0x3
   101e0:	41f5d513          	srai	a0,a1,0x1f
   101e4:	00178793          	addi	a5,a5,1 # 3001 <main-0xd073>
   101e8:	00f57533          	and	a0,a0,a5
   101ec:	00b50533          	add	a0,a0,a1
   101f0:	00008067          	ret

000101f4 <mq_rshift1>:
   101f4:	00157793          	andi	a5,a0,1
   101f8:	00003737          	lui	a4,0x3
   101fc:	00170713          	addi	a4,a4,1 # 3001 <main-0xd073>
   10200:	40f007b3          	neg	a5,a5
   10204:	00e7f7b3          	and	a5,a5,a4
   10208:	00a78533          	add	a0,a5,a0
   1020c:	00155513          	srli	a0,a0,0x1
   10210:	00008067          	ret

00010214 <mq_montymul>:
   10214:	02b50533          	mul	a0,a0,a1
   10218:	00151713          	slli	a4,a0,0x1
   1021c:	00a70733          	add	a4,a4,a0
   10220:	00c71713          	slli	a4,a4,0xc
   10224:	40a70733          	sub	a4,a4,a0
   10228:	01071713          	slli	a4,a4,0x10
   1022c:	01075713          	srli	a4,a4,0x10
   10230:	00171793          	slli	a5,a4,0x1
   10234:	00e787b3          	add	a5,a5,a4
   10238:	00c79793          	slli	a5,a5,0xc
   1023c:	00e787b3          	add	a5,a5,a4
   10240:	00a787b3          	add	a5,a5,a0
   10244:	ffffd737          	lui	a4,0xffffd
   10248:	fff70713          	addi	a4,a4,-1 # ffffcfff <__BSS_END__+0xfffe53fb>
   1024c:	0107d793          	srli	a5,a5,0x10
   10250:	00e787b3          	add	a5,a5,a4
   10254:	00003737          	lui	a4,0x3
   10258:	41f7d513          	srai	a0,a5,0x1f
   1025c:	00170713          	addi	a4,a4,1 # 3001 <main-0xd073>
   10260:	00e57533          	and	a0,a0,a4
   10264:	00f50533          	add	a0,a0,a5
   10268:	00008067          	ret

0001026c <PQCLEAN_FALCON512_CLEAN_is_short.constprop.0>:
   1026c:	000156b7          	lui	a3,0x15
   10270:	00015837          	lui	a6,0x15
   10274:	35268693          	addi	a3,a3,850 # 15352 <sig+0x2>
   10278:	75080813          	addi	a6,a6,1872 # 15750 <sig+0x400>
   1027c:	0f800713          	li	a4,248
   10280:	00000593          	li	a1,0
   10284:	00000613          	li	a2,0
   10288:	00c0006f          	j	10294 <PQCLEAN_FALCON512_CLEAN_is_short.constprop.0+0x28>
   1028c:	00069703          	lh	a4,0(a3)
   10290:	00268693          	addi	a3,a3,2
   10294:	00051783          	lh	a5,0(a0)
   10298:	02e70733          	mul	a4,a4,a4
   1029c:	00250513          	addi	a0,a0,2
   102a0:	02f787b3          	mul	a5,a5,a5
   102a4:	00c787b3          	add	a5,a5,a2
   102a8:	00f70633          	add	a2,a4,a5
   102ac:	00c7e7b3          	or	a5,a5,a2
   102b0:	00f5e5b3          	or	a1,a1,a5
   102b4:	fcd81ce3          	bne	a6,a3,1028c <PQCLEAN_FALCON512_CLEAN_is_short.constprop.0+0x20>
   102b8:	41f5d593          	srai	a1,a1,0x1f
   102bc:	02984537          	lui	a0,0x2984
   102c0:	00c5e5b3          	or	a1,a1,a2
   102c4:	5d650513          	addi	a0,a0,1494 # 29845d6 <__BSS_END__+0x296c9d2>
   102c8:	00a5b533          	sltu	a0,a1,a0
   102cc:	00008067          	ret

000102d0 <mq_iNTT.constprop.0>:
   102d0:	fa010113          	addi	sp,sp,-96
   102d4:	00900793          	li	a5,9
   102d8:	03a12823          	sw	s10,48(sp)
   102dc:	00f12a23          	sw	a5,20(sp)
   102e0:	00014d37          	lui	s10,0x14
   102e4:	20000793          	li	a5,512
   102e8:	04912a23          	sw	s1,84(sp)
   102ec:	00f12823          	sw	a5,16(sp)
   102f0:	000014b7          	lui	s1,0x1
   102f4:	b50d0793          	addi	a5,s10,-1200 # 13b50 <iGMb>
   102f8:	05412423          	sw	s4,72(sp)
   102fc:	05612023          	sw	s6,64(sp)
   10300:	04112e23          	sw	ra,92(sp)
   10304:	04812c23          	sw	s0,88(sp)
   10308:	05212823          	sw	s2,80(sp)
   1030c:	05312623          	sw	s3,76(sp)
   10310:	05512223          	sw	s5,68(sp)
   10314:	03712e23          	sw	s7,60(sp)
   10318:	03812c23          	sw	s8,56(sp)
   1031c:	03912a23          	sw	s9,52(sp)
   10320:	03b12623          	sw	s11,44(sp)
   10324:	00050a13          	mv	s4,a0
   10328:	5e148493          	addi	s1,s1,1505 # 15e1 <main-0xea93>
   1032c:	00100b13          	li	s6,1
   10330:	00f12c23          	sw	a5,24(sp)
   10334:	01012783          	lw	a5,16(sp)
   10338:	001b1b93          	slli	s7,s6,0x1
   1033c:	002b1713          	slli	a4,s6,0x2
   10340:	0017d793          	srli	a5,a5,0x1
   10344:	00178993          	addi	s3,a5,1
   10348:	00279a93          	slli	s5,a5,0x2
   1034c:	00f12e23          	sw	a5,28(sp)
   10350:	01812783          	lw	a5,24(sp)
   10354:	00199993          	slli	s3,s3,0x1
   10358:	00e12623          	sw	a4,12(sp)
   1035c:	013789b3          	add	s3,a5,s3
   10360:	017a0433          	add	s0,s4,s7
   10364:	01578ab3          	add	s5,a5,s5
   10368:	00000913          	li	s2,0
   1036c:	00191793          	slli	a5,s2,0x1
   10370:	012b06b3          	add	a3,s6,s2
   10374:	00fa0db3          	add	s11,s4,a5
   10378:	00040d13          	mv	s10,s0
   1037c:	04d97063          	bgeu	s2,a3,103bc <mq_iNTT.constprop.0+0xec>
   10380:	000ddc83          	lhu	s9,0(s11)
   10384:	000d5c03          	lhu	s8,0(s10)
   10388:	002d8d93          	addi	s11,s11,2
   1038c:	000c8513          	mv	a0,s9
   10390:	000c0593          	mv	a1,s8
   10394:	e1dff0ef          	jal	ra,101b0 <mq_add>
   10398:	fead9f23          	sh	a0,-2(s11)
   1039c:	000c0593          	mv	a1,s8
   103a0:	000c8513          	mv	a0,s9
   103a4:	e35ff0ef          	jal	ra,101d8 <mq_sub>
   103a8:	00048593          	mv	a1,s1
   103ac:	e69ff0ef          	jal	ra,10214 <mq_montymul>
   103b0:	00ad1023          	sh	a0,0(s10)
   103b4:	002d0d13          	addi	s10,s10,2
   103b8:	fdb414e3          	bne	s0,s11,10380 <mq_iNTT.constprop.0+0xb0>
   103bc:	00c12783          	lw	a5,12(sp)
   103c0:	01790933          	add	s2,s2,s7
   103c4:	00f40433          	add	s0,s0,a5
   103c8:	013a8863          	beq	s5,s3,103d8 <mq_iNTT.constprop.0+0x108>
   103cc:	0009d483          	lhu	s1,0(s3)
   103d0:	00298993          	addi	s3,s3,2
   103d4:	f99ff06f          	j	1036c <mq_iNTT.constprop.0+0x9c>
   103d8:	01412783          	lw	a5,20(sp)
   103dc:	fff78793          	addi	a5,a5,-1
   103e0:	00f12a23          	sw	a5,20(sp)
   103e4:	02078663          	beqz	a5,10410 <mq_iNTT.constprop.0+0x140>
   103e8:	01012783          	lw	a5,16(sp)
   103ec:	01812703          	lw	a4,24(sp)
   103f0:	000b8b13          	mv	s6,s7
   103f4:	0027d793          	srli	a5,a5,0x2
   103f8:	00179793          	slli	a5,a5,0x1
   103fc:	00f707b3          	add	a5,a4,a5
   10400:	0007d483          	lhu	s1,0(a5)
   10404:	01c12783          	lw	a5,28(sp)
   10408:	00f12823          	sw	a5,16(sp)
   1040c:	f29ff06f          	j	10334 <mq_iNTT.constprop.0+0x64>
   10410:	00001437          	lui	s0,0x1
   10414:	00900493          	li	s1,9
   10418:	ffb40413          	addi	s0,s0,-5 # ffb <main-0xf079>
   1041c:	00040513          	mv	a0,s0
   10420:	dd5ff0ef          	jal	ra,101f4 <mq_rshift1>
   10424:	fff48493          	addi	s1,s1,-1
   10428:	00050413          	mv	s0,a0
   1042c:	fe0498e3          	bnez	s1,1041c <mq_iNTT.constprop.0+0x14c>
   10430:	400a0493          	addi	s1,s4,1024
   10434:	000a5503          	lhu	a0,0(s4)
   10438:	00040593          	mv	a1,s0
   1043c:	002a0a13          	addi	s4,s4,2
   10440:	dd5ff0ef          	jal	ra,10214 <mq_montymul>
   10444:	feaa1f23          	sh	a0,-2(s4)
   10448:	ff4496e3          	bne	s1,s4,10434 <mq_iNTT.constprop.0+0x164>
   1044c:	05c12083          	lw	ra,92(sp)
   10450:	05812403          	lw	s0,88(sp)
   10454:	05412483          	lw	s1,84(sp)
   10458:	05012903          	lw	s2,80(sp)
   1045c:	04c12983          	lw	s3,76(sp)
   10460:	04812a03          	lw	s4,72(sp)
   10464:	04412a83          	lw	s5,68(sp)
   10468:	04012b03          	lw	s6,64(sp)
   1046c:	03c12b83          	lw	s7,60(sp)
   10470:	03812c03          	lw	s8,56(sp)
   10474:	03412c83          	lw	s9,52(sp)
   10478:	03012d03          	lw	s10,48(sp)
   1047c:	02c12d83          	lw	s11,44(sp)
   10480:	06010113          	addi	sp,sp,96
   10484:	00008067          	ret

00010488 <mq_NTT.constprop.0>:
   10488:	fb010113          	addi	sp,sp,-80
   1048c:	03a12023          	sw	s10,32(sp)
   10490:	00014d37          	lui	s10,0x14
   10494:	350d0713          	addi	a4,s10,848 # 14350 <GMb>
   10498:	00900793          	li	a5,9
   1049c:	04912223          	sw	s1,68(sp)
   104a0:	00e12423          	sw	a4,8(sp)
   104a4:	000024b7          	lui	s1,0x2
   104a8:	00200713          	li	a4,2
   104ac:	03512a23          	sw	s5,52(sp)
   104b0:	03712623          	sw	s7,44(sp)
   104b4:	00f12223          	sw	a5,4(sp)
   104b8:	04112623          	sw	ra,76(sp)
   104bc:	04812423          	sw	s0,72(sp)
   104c0:	05212023          	sw	s2,64(sp)
   104c4:	03312e23          	sw	s3,60(sp)
   104c8:	03412c23          	sw	s4,56(sp)
   104cc:	03612823          	sw	s6,48(sp)
   104d0:	03812423          	sw	s8,40(sp)
   104d4:	03912223          	sw	s9,36(sp)
   104d8:	01b12e23          	sw	s11,28(sp)
   104dc:	00050b93          	mv	s7,a0
   104e0:	ed048493          	addi	s1,s1,-304 # 1ed0 <main-0xe1a4>
   104e4:	00100793          	li	a5,1
   104e8:	20000a93          	li	s5,512
   104ec:	00e12623          	sw	a4,12(sp)
   104f0:	00812703          	lw	a4,8(sp)
   104f4:	00178993          	addi	s3,a5,1
   104f8:	001adb13          	srli	s6,s5,0x1
   104fc:	00279793          	slli	a5,a5,0x2
   10500:	00199993          	slli	s3,s3,0x1
   10504:	001b1413          	slli	s0,s6,0x1
   10508:	00f707b3          	add	a5,a4,a5
   1050c:	013709b3          	add	s3,a4,s3
   10510:	001a9c13          	slli	s8,s5,0x1
   10514:	008b8433          	add	s0,s7,s0
   10518:	00f12023          	sw	a5,0(sp)
   1051c:	00000913          	li	s2,0
   10520:	00191793          	slli	a5,s2,0x1
   10524:	012b06b3          	add	a3,s6,s2
   10528:	00fb8db3          	add	s11,s7,a5
   1052c:	00040d13          	mv	s10,s0
   10530:	04d97263          	bgeu	s2,a3,10574 <mq_NTT.constprop.0+0xec>
   10534:	000d5503          	lhu	a0,0(s10)
   10538:	000ddc83          	lhu	s9,0(s11)
   1053c:	00048593          	mv	a1,s1
   10540:	cd5ff0ef          	jal	ra,10214 <mq_montymul>
   10544:	00050593          	mv	a1,a0
   10548:	00050a13          	mv	s4,a0
   1054c:	000c8513          	mv	a0,s9
   10550:	c61ff0ef          	jal	ra,101b0 <mq_add>
   10554:	00ad9023          	sh	a0,0(s11)
   10558:	000a0593          	mv	a1,s4
   1055c:	000c8513          	mv	a0,s9
   10560:	c79ff0ef          	jal	ra,101d8 <mq_sub>
   10564:	00ad1023          	sh	a0,0(s10)
   10568:	002d8d93          	addi	s11,s11,2
   1056c:	002d0d13          	addi	s10,s10,2
   10570:	fdb412e3          	bne	s0,s11,10534 <mq_NTT.constprop.0+0xac>
   10574:	00012783          	lw	a5,0(sp)
   10578:	01590933          	add	s2,s2,s5
   1057c:	01840433          	add	s0,s0,s8
   10580:	00f98863          	beq	s3,a5,10590 <mq_NTT.constprop.0+0x108>
   10584:	0009d483          	lhu	s1,0(s3)
   10588:	00298993          	addi	s3,s3,2
   1058c:	f95ff06f          	j	10520 <mq_NTT.constprop.0+0x98>
   10590:	00412783          	lw	a5,4(sp)
   10594:	00c12683          	lw	a3,12(sp)
   10598:	fff78713          	addi	a4,a5,-1
   1059c:	00e12223          	sw	a4,4(sp)
   105a0:	00068793          	mv	a5,a3
   105a4:	02070063          	beqz	a4,105c4 <mq_NTT.constprop.0+0x13c>
   105a8:	00169713          	slli	a4,a3,0x1
   105ac:	00812683          	lw	a3,8(sp)
   105b0:	00e12623          	sw	a4,12(sp)
   105b4:	000b0a93          	mv	s5,s6
   105b8:	00e68733          	add	a4,a3,a4
   105bc:	00075483          	lhu	s1,0(a4)
   105c0:	f31ff06f          	j	104f0 <mq_NTT.constprop.0+0x68>
   105c4:	04c12083          	lw	ra,76(sp)
   105c8:	04812403          	lw	s0,72(sp)
   105cc:	04412483          	lw	s1,68(sp)
   105d0:	04012903          	lw	s2,64(sp)
   105d4:	03c12983          	lw	s3,60(sp)
   105d8:	03812a03          	lw	s4,56(sp)
   105dc:	03412a83          	lw	s5,52(sp)
   105e0:	03012b03          	lw	s6,48(sp)
   105e4:	02c12b83          	lw	s7,44(sp)
   105e8:	02812c03          	lw	s8,40(sp)
   105ec:	02412c83          	lw	s9,36(sp)
   105f0:	02012d03          	lw	s10,32(sp)
   105f4:	01c12d83          	lw	s11,28(sp)
   105f8:	05010113          	addi	sp,sp,80
   105fc:	00008067          	ret

00010600 <mq_poly_montymul_ntt.constprop.0>:
   10600:	ff010113          	addi	sp,sp,-16
   10604:	00812423          	sw	s0,8(sp)
   10608:	00015437          	lui	s0,0x15
   1060c:	b5040413          	addi	s0,s0,-1200 # 14b50 <h>
   10610:	000035b7          	lui	a1,0x3
   10614:	00912223          	sw	s1,4(sp)
   10618:	01212023          	sw	s2,0(sp)
   1061c:	00112623          	sw	ra,12(sp)
   10620:	00050493          	mv	s1,a0
   10624:	40040913          	addi	s2,s0,1024
   10628:	db058593          	addi	a1,a1,-592 # 2db0 <main-0xd2c4>
   1062c:	0080006f          	j	10634 <mq_poly_montymul_ntt.constprop.0+0x34>
   10630:	00045583          	lhu	a1,0(s0)
   10634:	0004d503          	lhu	a0,0(s1)
   10638:	00240413          	addi	s0,s0,2
   1063c:	00248493          	addi	s1,s1,2
   10640:	bd5ff0ef          	jal	ra,10214 <mq_montymul>
   10644:	fea49f23          	sh	a0,-2(s1)
   10648:	fe8914e3          	bne	s2,s0,10630 <mq_poly_montymul_ntt.constprop.0+0x30>
   1064c:	00c12083          	lw	ra,12(sp)
   10650:	00812403          	lw	s0,8(sp)
   10654:	00412483          	lw	s1,4(sp)
   10658:	00012903          	lw	s2,0(sp)
   1065c:	01010113          	addi	sp,sp,16
   10660:	00008067          	ret

00010664 <mq_poly_sub.constprop.0>:
   10664:	ff010113          	addi	sp,sp,-16
   10668:	00812423          	sw	s0,8(sp)
   1066c:	00016437          	lui	s0,0x16
   10670:	b5040413          	addi	s0,s0,-1200 # 15b50 <hm>
   10674:	000015b7          	lui	a1,0x1
   10678:	00912223          	sw	s1,4(sp)
   1067c:	01212023          	sw	s2,0(sp)
   10680:	00112623          	sw	ra,12(sp)
   10684:	00050493          	mv	s1,a0
   10688:	40040913          	addi	s2,s0,1024
   1068c:	c1558593          	addi	a1,a1,-1003 # c15 <main-0xf45f>
   10690:	0080006f          	j	10698 <mq_poly_sub.constprop.0+0x34>
   10694:	00045583          	lhu	a1,0(s0)
   10698:	0004d503          	lhu	a0,0(s1)
   1069c:	00240413          	addi	s0,s0,2
   106a0:	00248493          	addi	s1,s1,2
   106a4:	b35ff0ef          	jal	ra,101d8 <mq_sub>
   106a8:	fea49f23          	sh	a0,-2(s1)
   106ac:	fe8914e3          	bne	s2,s0,10694 <mq_poly_sub.constprop.0+0x30>
   106b0:	00c12083          	lw	ra,12(sp)
   106b4:	00812403          	lw	s0,8(sp)
   106b8:	00412483          	lw	s1,4(sp)
   106bc:	00012903          	lw	s2,0(sp)
   106c0:	01010113          	addi	sp,sp,16
   106c4:	00008067          	ret

000106c8 <PQCLEAN_FALCON512_CLEAN_verify_raw.constprop.0>:
   106c8:	ff010113          	addi	sp,sp,-16
   106cc:	00015737          	lui	a4,0x15
   106d0:	00015837          	lui	a6,0x15
   106d4:	000035b7          	lui	a1,0x3
   106d8:	00812423          	sw	s0,8(sp)
   106dc:	00912223          	sw	s1,4(sp)
   106e0:	00112623          	sw	ra,12(sp)
   106e4:	00050493          	mv	s1,a0
   106e8:	00050413          	mv	s0,a0
   106ec:	35270713          	addi	a4,a4,850 # 15352 <sig+0x2>
   106f0:	75080813          	addi	a6,a6,1872 # 15750 <sig+0x400>
   106f4:	00050693          	mv	a3,a0
   106f8:	0f800613          	li	a2,248
   106fc:	00158593          	addi	a1,a1,1 # 3001 <main-0xd073>
   10700:	00c0006f          	j	1070c <PQCLEAN_FALCON512_CLEAN_verify_raw.constprop.0+0x44>
   10704:	00071603          	lh	a2,0(a4)
   10708:	00270713          	addi	a4,a4,2
   1070c:	41f65793          	srai	a5,a2,0x1f
   10710:	00b7f7b3          	and	a5,a5,a1
   10714:	00c787b3          	add	a5,a5,a2
   10718:	00f69023          	sh	a5,0(a3)
   1071c:	00268693          	addi	a3,a3,2
   10720:	fee812e3          	bne	a6,a4,10704 <PQCLEAN_FALCON512_CLEAN_verify_raw.constprop.0+0x3c>
   10724:	00048513          	mv	a0,s1
   10728:	d61ff0ef          	jal	ra,10488 <mq_NTT.constprop.0>
   1072c:	00048513          	mv	a0,s1
   10730:	ed1ff0ef          	jal	ra,10600 <mq_poly_montymul_ntt.constprop.0>
   10734:	00048513          	mv	a0,s1
   10738:	b99ff0ef          	jal	ra,102d0 <mq_iNTT.constprop.0>
   1073c:	00048513          	mv	a0,s1
   10740:	f25ff0ef          	jal	ra,10664 <mq_poly_sub.constprop.0>
   10744:	00002637          	lui	a2,0x2
   10748:	000036b7          	lui	a3,0x3
   1074c:	40048593          	addi	a1,s1,1024
   10750:	80060613          	addi	a2,a2,-2048 # 1800 <main-0xe874>
   10754:	00168693          	addi	a3,a3,1 # 3001 <main-0xd073>
   10758:	00045703          	lhu	a4,0(s0)
   1075c:	00240413          	addi	s0,s0,2
   10760:	40e607b3          	sub	a5,a2,a4
   10764:	41f7d793          	srai	a5,a5,0x1f
   10768:	00d7f7b3          	and	a5,a5,a3
   1076c:	40f70733          	sub	a4,a4,a5
   10770:	fee41f23          	sh	a4,-2(s0)
   10774:	fe8592e3          	bne	a1,s0,10758 <PQCLEAN_FALCON512_CLEAN_verify_raw.constprop.0+0x90>
   10778:	00812403          	lw	s0,8(sp)
   1077c:	00c12083          	lw	ra,12(sp)
   10780:	00048513          	mv	a0,s1
   10784:	00412483          	lw	s1,4(sp)
   10788:	01010113          	addi	sp,sp,16
   1078c:	ae1ff06f          	j	1026c <PQCLEAN_FALCON512_CLEAN_is_short.constprop.0>

00010790 <exit>:
   10790:	ff010113          	addi	sp,sp,-16
   10794:	00000593          	li	a1,0
   10798:	00812423          	sw	s0,8(sp)
   1079c:	00112623          	sw	ra,12(sp)
   107a0:	00050413          	mv	s0,a0
   107a4:	2f0000ef          	jal	ra,10a94 <__call_exitprocs>
   107a8:	0301a503          	lw	a0,48(gp) # 17b98 <_global_impure_ptr>
   107ac:	03c52783          	lw	a5,60(a0)
   107b0:	00078463          	beqz	a5,107b8 <exit+0x28>
   107b4:	000780e7          	jalr	a5
   107b8:	00040513          	mv	a0,s0
   107bc:	0b8030ef          	jal	ra,13874 <_exit>

000107c0 <__libc_init_array>:
   107c0:	ff010113          	addi	sp,sp,-16
   107c4:	00812423          	sw	s0,8(sp)
   107c8:	01212023          	sw	s2,0(sp)
   107cc:	00007417          	auipc	s0,0x7
   107d0:	b8c40413          	addi	s0,s0,-1140 # 17358 <__init_array_start>
   107d4:	00007917          	auipc	s2,0x7
   107d8:	b8490913          	addi	s2,s2,-1148 # 17358 <__init_array_start>
   107dc:	40890933          	sub	s2,s2,s0
   107e0:	00112623          	sw	ra,12(sp)
   107e4:	00912223          	sw	s1,4(sp)
   107e8:	40295913          	srai	s2,s2,0x2
   107ec:	00090e63          	beqz	s2,10808 <__libc_init_array+0x48>
   107f0:	00000493          	li	s1,0
   107f4:	00042783          	lw	a5,0(s0)
   107f8:	00148493          	addi	s1,s1,1
   107fc:	00440413          	addi	s0,s0,4
   10800:	000780e7          	jalr	a5
   10804:	fe9918e3          	bne	s2,s1,107f4 <__libc_init_array+0x34>
   10808:	00007417          	auipc	s0,0x7
   1080c:	b5040413          	addi	s0,s0,-1200 # 17358 <__init_array_start>
   10810:	00007917          	auipc	s2,0x7
   10814:	b5090913          	addi	s2,s2,-1200 # 17360 <__do_global_dtors_aux_fini_array_entry>
   10818:	40890933          	sub	s2,s2,s0
   1081c:	40295913          	srai	s2,s2,0x2
   10820:	00090e63          	beqz	s2,1083c <__libc_init_array+0x7c>
   10824:	00000493          	li	s1,0
   10828:	00042783          	lw	a5,0(s0)
   1082c:	00148493          	addi	s1,s1,1
   10830:	00440413          	addi	s0,s0,4
   10834:	000780e7          	jalr	a5
   10838:	fe9918e3          	bne	s2,s1,10828 <__libc_init_array+0x68>
   1083c:	00c12083          	lw	ra,12(sp)
   10840:	00812403          	lw	s0,8(sp)
   10844:	00412483          	lw	s1,4(sp)
   10848:	00012903          	lw	s2,0(sp)
   1084c:	01010113          	addi	sp,sp,16
   10850:	00008067          	ret

00010854 <memset>:
   10854:	00f00313          	li	t1,15
   10858:	00050713          	mv	a4,a0
   1085c:	02c37e63          	bgeu	t1,a2,10898 <memset+0x44>
   10860:	00f77793          	andi	a5,a4,15
   10864:	0a079063          	bnez	a5,10904 <memset+0xb0>
   10868:	08059263          	bnez	a1,108ec <memset+0x98>
   1086c:	ff067693          	andi	a3,a2,-16
   10870:	00f67613          	andi	a2,a2,15
   10874:	00e686b3          	add	a3,a3,a4
   10878:	00b72023          	sw	a1,0(a4)
   1087c:	00b72223          	sw	a1,4(a4)
   10880:	00b72423          	sw	a1,8(a4)
   10884:	00b72623          	sw	a1,12(a4)
   10888:	01070713          	addi	a4,a4,16
   1088c:	fed766e3          	bltu	a4,a3,10878 <memset+0x24>
   10890:	00061463          	bnez	a2,10898 <memset+0x44>
   10894:	00008067          	ret
   10898:	40c306b3          	sub	a3,t1,a2
   1089c:	00269693          	slli	a3,a3,0x2
   108a0:	00000297          	auipc	t0,0x0
   108a4:	005686b3          	add	a3,a3,t0
   108a8:	00c68067          	jr	12(a3)
   108ac:	00b70723          	sb	a1,14(a4)
   108b0:	00b706a3          	sb	a1,13(a4)
   108b4:	00b70623          	sb	a1,12(a4)
   108b8:	00b705a3          	sb	a1,11(a4)
   108bc:	00b70523          	sb	a1,10(a4)
   108c0:	00b704a3          	sb	a1,9(a4)
   108c4:	00b70423          	sb	a1,8(a4)
   108c8:	00b703a3          	sb	a1,7(a4)
   108cc:	00b70323          	sb	a1,6(a4)
   108d0:	00b702a3          	sb	a1,5(a4)
   108d4:	00b70223          	sb	a1,4(a4)
   108d8:	00b701a3          	sb	a1,3(a4)
   108dc:	00b70123          	sb	a1,2(a4)
   108e0:	00b700a3          	sb	a1,1(a4)
   108e4:	00b70023          	sb	a1,0(a4)
   108e8:	00008067          	ret
   108ec:	0ff5f593          	zext.b	a1,a1
   108f0:	00859693          	slli	a3,a1,0x8
   108f4:	00d5e5b3          	or	a1,a1,a3
   108f8:	01059693          	slli	a3,a1,0x10
   108fc:	00d5e5b3          	or	a1,a1,a3
   10900:	f6dff06f          	j	1086c <memset+0x18>
   10904:	00279693          	slli	a3,a5,0x2
   10908:	00000297          	auipc	t0,0x0
   1090c:	005686b3          	add	a3,a3,t0
   10910:	00008293          	mv	t0,ra
   10914:	fa0680e7          	jalr	-96(a3)
   10918:	00028093          	mv	ra,t0
   1091c:	ff078793          	addi	a5,a5,-16
   10920:	40f70733          	sub	a4,a4,a5
   10924:	00f60633          	add	a2,a2,a5
   10928:	f6c378e3          	bgeu	t1,a2,10898 <memset+0x44>
   1092c:	f3dff06f          	j	10868 <memset+0x14>

00010930 <_puts_r>:
   10930:	fc010113          	addi	sp,sp,-64
   10934:	02812c23          	sw	s0,56(sp)
   10938:	00050413          	mv	s0,a0
   1093c:	00058513          	mv	a0,a1
   10940:	02912a23          	sw	s1,52(sp)
   10944:	02112e23          	sw	ra,60(sp)
   10948:	00058493          	mv	s1,a1
   1094c:	0bc000ef          	jal	ra,10a08 <strlen>
   10950:	00150713          	addi	a4,a0,1
   10954:	00006697          	auipc	a3,0x6
   10958:	9fc68693          	addi	a3,a3,-1540 # 16350 <hm+0x800>
   1095c:	00e12e23          	sw	a4,28(sp)
   10960:	03842783          	lw	a5,56(s0)
   10964:	02010713          	addi	a4,sp,32
   10968:	02d12423          	sw	a3,40(sp)
   1096c:	00e12a23          	sw	a4,20(sp)
   10970:	00100693          	li	a3,1
   10974:	00200713          	li	a4,2
   10978:	02912023          	sw	s1,32(sp)
   1097c:	02a12223          	sw	a0,36(sp)
   10980:	02d12623          	sw	a3,44(sp)
   10984:	00e12c23          	sw	a4,24(sp)
   10988:	00842583          	lw	a1,8(s0)
   1098c:	04078e63          	beqz	a5,109e8 <_puts_r+0xb8>
   10990:	00c59783          	lh	a5,12(a1)
   10994:	01279713          	slli	a4,a5,0x12
   10998:	02074263          	bltz	a4,109bc <_puts_r+0x8c>
   1099c:	0645a703          	lw	a4,100(a1)
   109a0:	000026b7          	lui	a3,0x2
   109a4:	00d7e7b3          	or	a5,a5,a3
   109a8:	ffffe6b7          	lui	a3,0xffffe
   109ac:	fff68693          	addi	a3,a3,-1 # ffffdfff <__BSS_END__+0xfffe63fb>
   109b0:	00d77733          	and	a4,a4,a3
   109b4:	00f59623          	sh	a5,12(a1)
   109b8:	06e5a223          	sw	a4,100(a1)
   109bc:	01410613          	addi	a2,sp,20
   109c0:	00040513          	mv	a0,s0
   109c4:	5f0000ef          	jal	ra,10fb4 <__sfvwrite_r>
   109c8:	03c12083          	lw	ra,60(sp)
   109cc:	03812403          	lw	s0,56(sp)
   109d0:	00a03533          	snez	a0,a0
   109d4:	40a00533          	neg	a0,a0
   109d8:	03412483          	lw	s1,52(sp)
   109dc:	00a56513          	ori	a0,a0,10
   109e0:	04010113          	addi	sp,sp,64
   109e4:	00008067          	ret
   109e8:	00040513          	mv	a0,s0
   109ec:	00b12623          	sw	a1,12(sp)
   109f0:	528000ef          	jal	ra,10f18 <__sinit>
   109f4:	00c12583          	lw	a1,12(sp)
   109f8:	f99ff06f          	j	10990 <_puts_r+0x60>

000109fc <puts>:
   109fc:	00050593          	mv	a1,a0
   10a00:	0381a503          	lw	a0,56(gp) # 17ba0 <_impure_ptr>
   10a04:	f2dff06f          	j	10930 <_puts_r>

00010a08 <strlen>:
   10a08:	00357793          	andi	a5,a0,3
   10a0c:	00050713          	mv	a4,a0
   10a10:	04079c63          	bnez	a5,10a68 <strlen+0x60>
   10a14:	7f7f86b7          	lui	a3,0x7f7f8
   10a18:	f7f68693          	addi	a3,a3,-129 # 7f7f7f7f <__BSS_END__+0x7f7e037b>
   10a1c:	fff00593          	li	a1,-1
   10a20:	00072603          	lw	a2,0(a4)
   10a24:	00470713          	addi	a4,a4,4
   10a28:	00d677b3          	and	a5,a2,a3
   10a2c:	00d787b3          	add	a5,a5,a3
   10a30:	00c7e7b3          	or	a5,a5,a2
   10a34:	00d7e7b3          	or	a5,a5,a3
   10a38:	feb784e3          	beq	a5,a1,10a20 <strlen+0x18>
   10a3c:	ffc74683          	lbu	a3,-4(a4)
   10a40:	40a707b3          	sub	a5,a4,a0
   10a44:	04068463          	beqz	a3,10a8c <strlen+0x84>
   10a48:	ffd74683          	lbu	a3,-3(a4)
   10a4c:	02068c63          	beqz	a3,10a84 <strlen+0x7c>
   10a50:	ffe74503          	lbu	a0,-2(a4)
   10a54:	00a03533          	snez	a0,a0
   10a58:	00f50533          	add	a0,a0,a5
   10a5c:	ffe50513          	addi	a0,a0,-2
   10a60:	00008067          	ret
   10a64:	fa0688e3          	beqz	a3,10a14 <strlen+0xc>
   10a68:	00074783          	lbu	a5,0(a4)
   10a6c:	00170713          	addi	a4,a4,1
   10a70:	00377693          	andi	a3,a4,3
   10a74:	fe0798e3          	bnez	a5,10a64 <strlen+0x5c>
   10a78:	40a70733          	sub	a4,a4,a0
   10a7c:	fff70513          	addi	a0,a4,-1
   10a80:	00008067          	ret
   10a84:	ffd78513          	addi	a0,a5,-3
   10a88:	00008067          	ret
   10a8c:	ffc78513          	addi	a0,a5,-4
   10a90:	00008067          	ret

00010a94 <__call_exitprocs>:
   10a94:	fd010113          	addi	sp,sp,-48
   10a98:	01412c23          	sw	s4,24(sp)
   10a9c:	0301aa03          	lw	s4,48(gp) # 17b98 <_global_impure_ptr>
   10aa0:	03212023          	sw	s2,32(sp)
   10aa4:	148a2903          	lw	s2,328(s4)
   10aa8:	02112623          	sw	ra,44(sp)
   10aac:	02812423          	sw	s0,40(sp)
   10ab0:	02912223          	sw	s1,36(sp)
   10ab4:	01312e23          	sw	s3,28(sp)
   10ab8:	01512a23          	sw	s5,20(sp)
   10abc:	01612823          	sw	s6,16(sp)
   10ac0:	01712623          	sw	s7,12(sp)
   10ac4:	01812423          	sw	s8,8(sp)
   10ac8:	04090063          	beqz	s2,10b08 <__call_exitprocs+0x74>
   10acc:	00050b13          	mv	s6,a0
   10ad0:	00058b93          	mv	s7,a1
   10ad4:	00100a93          	li	s5,1
   10ad8:	fff00993          	li	s3,-1
   10adc:	00492483          	lw	s1,4(s2)
   10ae0:	fff48413          	addi	s0,s1,-1
   10ae4:	02044263          	bltz	s0,10b08 <__call_exitprocs+0x74>
   10ae8:	00249493          	slli	s1,s1,0x2
   10aec:	009904b3          	add	s1,s2,s1
   10af0:	040b8463          	beqz	s7,10b38 <__call_exitprocs+0xa4>
   10af4:	1044a783          	lw	a5,260(s1)
   10af8:	05778063          	beq	a5,s7,10b38 <__call_exitprocs+0xa4>
   10afc:	fff40413          	addi	s0,s0,-1
   10b00:	ffc48493          	addi	s1,s1,-4
   10b04:	ff3416e3          	bne	s0,s3,10af0 <__call_exitprocs+0x5c>
   10b08:	02c12083          	lw	ra,44(sp)
   10b0c:	02812403          	lw	s0,40(sp)
   10b10:	02412483          	lw	s1,36(sp)
   10b14:	02012903          	lw	s2,32(sp)
   10b18:	01c12983          	lw	s3,28(sp)
   10b1c:	01812a03          	lw	s4,24(sp)
   10b20:	01412a83          	lw	s5,20(sp)
   10b24:	01012b03          	lw	s6,16(sp)
   10b28:	00c12b83          	lw	s7,12(sp)
   10b2c:	00812c03          	lw	s8,8(sp)
   10b30:	03010113          	addi	sp,sp,48
   10b34:	00008067          	ret
   10b38:	00492783          	lw	a5,4(s2)
   10b3c:	0044a683          	lw	a3,4(s1)
   10b40:	fff78793          	addi	a5,a5,-1
   10b44:	04878e63          	beq	a5,s0,10ba0 <__call_exitprocs+0x10c>
   10b48:	0004a223          	sw	zero,4(s1)
   10b4c:	fa0688e3          	beqz	a3,10afc <__call_exitprocs+0x68>
   10b50:	18892783          	lw	a5,392(s2)
   10b54:	008a9733          	sll	a4,s5,s0
   10b58:	00492c03          	lw	s8,4(s2)
   10b5c:	00f777b3          	and	a5,a4,a5
   10b60:	02079263          	bnez	a5,10b84 <__call_exitprocs+0xf0>
   10b64:	000680e7          	jalr	a3
   10b68:	00492703          	lw	a4,4(s2)
   10b6c:	148a2783          	lw	a5,328(s4)
   10b70:	01871463          	bne	a4,s8,10b78 <__call_exitprocs+0xe4>
   10b74:	f92784e3          	beq	a5,s2,10afc <__call_exitprocs+0x68>
   10b78:	f80788e3          	beqz	a5,10b08 <__call_exitprocs+0x74>
   10b7c:	00078913          	mv	s2,a5
   10b80:	f5dff06f          	j	10adc <__call_exitprocs+0x48>
   10b84:	18c92783          	lw	a5,396(s2)
   10b88:	0844a583          	lw	a1,132(s1)
   10b8c:	00f77733          	and	a4,a4,a5
   10b90:	00071c63          	bnez	a4,10ba8 <__call_exitprocs+0x114>
   10b94:	000b0513          	mv	a0,s6
   10b98:	000680e7          	jalr	a3
   10b9c:	fcdff06f          	j	10b68 <__call_exitprocs+0xd4>
   10ba0:	00892223          	sw	s0,4(s2)
   10ba4:	fa9ff06f          	j	10b4c <__call_exitprocs+0xb8>
   10ba8:	00058513          	mv	a0,a1
   10bac:	000680e7          	jalr	a3
   10bb0:	fb9ff06f          	j	10b68 <__call_exitprocs+0xd4>

00010bb4 <atexit>:
   10bb4:	00050593          	mv	a1,a0
   10bb8:	00000693          	li	a3,0
   10bbc:	00000613          	li	a2,0
   10bc0:	00000513          	li	a0,0
   10bc4:	57d0106f          	j	12940 <__register_exitproc>

00010bc8 <__fp_lock>:
   10bc8:	00000513          	li	a0,0
   10bcc:	00008067          	ret

00010bd0 <_cleanup_r>:
   10bd0:	00002597          	auipc	a1,0x2
   10bd4:	e5858593          	addi	a1,a1,-424 # 12a28 <_fclose_r>
   10bd8:	1310006f          	j	11508 <_fwalk_reent>

00010bdc <__fp_unlock>:
   10bdc:	00000513          	li	a0,0
   10be0:	00008067          	ret

00010be4 <__sinit.part.0>:
   10be4:	fe010113          	addi	sp,sp,-32
   10be8:	00112e23          	sw	ra,28(sp)
   10bec:	00812c23          	sw	s0,24(sp)
   10bf0:	00912a23          	sw	s1,20(sp)
   10bf4:	01212823          	sw	s2,16(sp)
   10bf8:	01312623          	sw	s3,12(sp)
   10bfc:	01412423          	sw	s4,8(sp)
   10c00:	01512223          	sw	s5,4(sp)
   10c04:	01612023          	sw	s6,0(sp)
   10c08:	00452403          	lw	s0,4(a0)
   10c0c:	00000717          	auipc	a4,0x0
   10c10:	fc470713          	addi	a4,a4,-60 # 10bd0 <_cleanup_r>
   10c14:	02e52e23          	sw	a4,60(a0)
   10c18:	2ec50793          	addi	a5,a0,748
   10c1c:	00300713          	li	a4,3
   10c20:	2ee52223          	sw	a4,740(a0)
   10c24:	2ef52423          	sw	a5,744(a0)
   10c28:	2e052023          	sw	zero,736(a0)
   10c2c:	00400793          	li	a5,4
   10c30:	00050913          	mv	s2,a0
   10c34:	00f42623          	sw	a5,12(s0)
   10c38:	00800613          	li	a2,8
   10c3c:	00000593          	li	a1,0
   10c40:	06042223          	sw	zero,100(s0)
   10c44:	00042023          	sw	zero,0(s0)
   10c48:	00042223          	sw	zero,4(s0)
   10c4c:	00042423          	sw	zero,8(s0)
   10c50:	00042823          	sw	zero,16(s0)
   10c54:	00042a23          	sw	zero,20(s0)
   10c58:	00042c23          	sw	zero,24(s0)
   10c5c:	05c40513          	addi	a0,s0,92
   10c60:	bf5ff0ef          	jal	ra,10854 <memset>
   10c64:	00892483          	lw	s1,8(s2)
   10c68:	00002b17          	auipc	s6,0x2
   10c6c:	9b8b0b13          	addi	s6,s6,-1608 # 12620 <__sread>
   10c70:	00002a97          	auipc	s5,0x2
   10c74:	a14a8a93          	addi	s5,s5,-1516 # 12684 <__swrite>
   10c78:	00002a17          	auipc	s4,0x2
   10c7c:	a94a0a13          	addi	s4,s4,-1388 # 1270c <__sseek>
   10c80:	00002997          	auipc	s3,0x2
   10c84:	af498993          	addi	s3,s3,-1292 # 12774 <__sclose>
   10c88:	000107b7          	lui	a5,0x10
   10c8c:	03642023          	sw	s6,32(s0)
   10c90:	03542223          	sw	s5,36(s0)
   10c94:	03442423          	sw	s4,40(s0)
   10c98:	03342623          	sw	s3,44(s0)
   10c9c:	00842e23          	sw	s0,28(s0)
   10ca0:	00978793          	addi	a5,a5,9 # 10009 <main-0x6b>
   10ca4:	00f4a623          	sw	a5,12(s1)
   10ca8:	00800613          	li	a2,8
   10cac:	00000593          	li	a1,0
   10cb0:	0604a223          	sw	zero,100(s1)
   10cb4:	0004a023          	sw	zero,0(s1)
   10cb8:	0004a223          	sw	zero,4(s1)
   10cbc:	0004a423          	sw	zero,8(s1)
   10cc0:	0004a823          	sw	zero,16(s1)
   10cc4:	0004aa23          	sw	zero,20(s1)
   10cc8:	0004ac23          	sw	zero,24(s1)
   10ccc:	05c48513          	addi	a0,s1,92
   10cd0:	b85ff0ef          	jal	ra,10854 <memset>
   10cd4:	00c92403          	lw	s0,12(s2)
   10cd8:	000207b7          	lui	a5,0x20
   10cdc:	0364a023          	sw	s6,32(s1)
   10ce0:	0354a223          	sw	s5,36(s1)
   10ce4:	0344a423          	sw	s4,40(s1)
   10ce8:	0334a623          	sw	s3,44(s1)
   10cec:	0094ae23          	sw	s1,28(s1)
   10cf0:	01278793          	addi	a5,a5,18 # 20012 <__BSS_END__+0x840e>
   10cf4:	00f42623          	sw	a5,12(s0)
   10cf8:	06042223          	sw	zero,100(s0)
   10cfc:	00042023          	sw	zero,0(s0)
   10d00:	00042223          	sw	zero,4(s0)
   10d04:	00042423          	sw	zero,8(s0)
   10d08:	00042823          	sw	zero,16(s0)
   10d0c:	00042a23          	sw	zero,20(s0)
   10d10:	00042c23          	sw	zero,24(s0)
   10d14:	05c40513          	addi	a0,s0,92
   10d18:	00800613          	li	a2,8
   10d1c:	00000593          	li	a1,0
   10d20:	b35ff0ef          	jal	ra,10854 <memset>
   10d24:	01c12083          	lw	ra,28(sp)
   10d28:	03642023          	sw	s6,32(s0)
   10d2c:	03542223          	sw	s5,36(s0)
   10d30:	03442423          	sw	s4,40(s0)
   10d34:	03342623          	sw	s3,44(s0)
   10d38:	00842e23          	sw	s0,28(s0)
   10d3c:	01812403          	lw	s0,24(sp)
   10d40:	00100793          	li	a5,1
   10d44:	02f92c23          	sw	a5,56(s2)
   10d48:	01412483          	lw	s1,20(sp)
   10d4c:	01012903          	lw	s2,16(sp)
   10d50:	00c12983          	lw	s3,12(sp)
   10d54:	00812a03          	lw	s4,8(sp)
   10d58:	00412a83          	lw	s5,4(sp)
   10d5c:	00012b03          	lw	s6,0(sp)
   10d60:	02010113          	addi	sp,sp,32
   10d64:	00008067          	ret

00010d68 <__sfmoreglue>:
   10d68:	ff010113          	addi	sp,sp,-16
   10d6c:	00912223          	sw	s1,4(sp)
   10d70:	06800793          	li	a5,104
   10d74:	fff58493          	addi	s1,a1,-1
   10d78:	02f484b3          	mul	s1,s1,a5
   10d7c:	01212023          	sw	s2,0(sp)
   10d80:	00058913          	mv	s2,a1
   10d84:	00812423          	sw	s0,8(sp)
   10d88:	00112623          	sw	ra,12(sp)
   10d8c:	07448593          	addi	a1,s1,116
   10d90:	02d000ef          	jal	ra,115bc <_malloc_r>
   10d94:	00050413          	mv	s0,a0
   10d98:	02050063          	beqz	a0,10db8 <__sfmoreglue+0x50>
   10d9c:	00c50513          	addi	a0,a0,12
   10da0:	00042023          	sw	zero,0(s0)
   10da4:	01242223          	sw	s2,4(s0)
   10da8:	00a42423          	sw	a0,8(s0)
   10dac:	06848613          	addi	a2,s1,104
   10db0:	00000593          	li	a1,0
   10db4:	aa1ff0ef          	jal	ra,10854 <memset>
   10db8:	00c12083          	lw	ra,12(sp)
   10dbc:	00040513          	mv	a0,s0
   10dc0:	00812403          	lw	s0,8(sp)
   10dc4:	00412483          	lw	s1,4(sp)
   10dc8:	00012903          	lw	s2,0(sp)
   10dcc:	01010113          	addi	sp,sp,16
   10dd0:	00008067          	ret

00010dd4 <__sfp>:
   10dd4:	fe010113          	addi	sp,sp,-32
   10dd8:	01212823          	sw	s2,16(sp)
   10ddc:	0301a903          	lw	s2,48(gp) # 17b98 <_global_impure_ptr>
   10de0:	03892783          	lw	a5,56(s2)
   10de4:	01312623          	sw	s3,12(sp)
   10de8:	00112e23          	sw	ra,28(sp)
   10dec:	00812c23          	sw	s0,24(sp)
   10df0:	00912a23          	sw	s1,20(sp)
   10df4:	01412423          	sw	s4,8(sp)
   10df8:	00050993          	mv	s3,a0
   10dfc:	0a078a63          	beqz	a5,10eb0 <__sfp+0xdc>
   10e00:	2e090913          	addi	s2,s2,736
   10e04:	fff00493          	li	s1,-1
   10e08:	00400a13          	li	s4,4
   10e0c:	00492783          	lw	a5,4(s2)
   10e10:	00892403          	lw	s0,8(s2)
   10e14:	fff78793          	addi	a5,a5,-1
   10e18:	0007d863          	bgez	a5,10e28 <__sfp+0x54>
   10e1c:	0840006f          	j	10ea0 <__sfp+0xcc>
   10e20:	06840413          	addi	s0,s0,104
   10e24:	06978e63          	beq	a5,s1,10ea0 <__sfp+0xcc>
   10e28:	00c41703          	lh	a4,12(s0)
   10e2c:	fff78793          	addi	a5,a5,-1
   10e30:	fe0718e3          	bnez	a4,10e20 <__sfp+0x4c>
   10e34:	ffff07b7          	lui	a5,0xffff0
   10e38:	00178793          	addi	a5,a5,1 # ffff0001 <__BSS_END__+0xfffd83fd>
   10e3c:	06042223          	sw	zero,100(s0)
   10e40:	00042023          	sw	zero,0(s0)
   10e44:	00042223          	sw	zero,4(s0)
   10e48:	00042423          	sw	zero,8(s0)
   10e4c:	00f42623          	sw	a5,12(s0)
   10e50:	00042823          	sw	zero,16(s0)
   10e54:	00042a23          	sw	zero,20(s0)
   10e58:	00042c23          	sw	zero,24(s0)
   10e5c:	00800613          	li	a2,8
   10e60:	00000593          	li	a1,0
   10e64:	05c40513          	addi	a0,s0,92
   10e68:	9edff0ef          	jal	ra,10854 <memset>
   10e6c:	02042823          	sw	zero,48(s0)
   10e70:	02042a23          	sw	zero,52(s0)
   10e74:	04042223          	sw	zero,68(s0)
   10e78:	04042423          	sw	zero,72(s0)
   10e7c:	01c12083          	lw	ra,28(sp)
   10e80:	00040513          	mv	a0,s0
   10e84:	01812403          	lw	s0,24(sp)
   10e88:	01412483          	lw	s1,20(sp)
   10e8c:	01012903          	lw	s2,16(sp)
   10e90:	00c12983          	lw	s3,12(sp)
   10e94:	00812a03          	lw	s4,8(sp)
   10e98:	02010113          	addi	sp,sp,32
   10e9c:	00008067          	ret
   10ea0:	00092403          	lw	s0,0(s2)
   10ea4:	00040c63          	beqz	s0,10ebc <__sfp+0xe8>
   10ea8:	00040913          	mv	s2,s0
   10eac:	f61ff06f          	j	10e0c <__sfp+0x38>
   10eb0:	00090513          	mv	a0,s2
   10eb4:	d31ff0ef          	jal	ra,10be4 <__sinit.part.0>
   10eb8:	f49ff06f          	j	10e00 <__sfp+0x2c>
   10ebc:	1ac00593          	li	a1,428
   10ec0:	00098513          	mv	a0,s3
   10ec4:	6f8000ef          	jal	ra,115bc <_malloc_r>
   10ec8:	00050413          	mv	s0,a0
   10ecc:	02050663          	beqz	a0,10ef8 <__sfp+0x124>
   10ed0:	00c50513          	addi	a0,a0,12
   10ed4:	00042023          	sw	zero,0(s0)
   10ed8:	01442223          	sw	s4,4(s0)
   10edc:	00a42423          	sw	a0,8(s0)
   10ee0:	1a000613          	li	a2,416
   10ee4:	00000593          	li	a1,0
   10ee8:	96dff0ef          	jal	ra,10854 <memset>
   10eec:	00892023          	sw	s0,0(s2)
   10ef0:	00040913          	mv	s2,s0
   10ef4:	f19ff06f          	j	10e0c <__sfp+0x38>
   10ef8:	00092023          	sw	zero,0(s2)
   10efc:	00c00793          	li	a5,12
   10f00:	00f9a023          	sw	a5,0(s3)
   10f04:	f79ff06f          	j	10e7c <__sfp+0xa8>

00010f08 <_cleanup>:
   10f08:	00002597          	auipc	a1,0x2
   10f0c:	b2058593          	addi	a1,a1,-1248 # 12a28 <_fclose_r>
   10f10:	0301a503          	lw	a0,48(gp) # 17b98 <_global_impure_ptr>
   10f14:	5f40006f          	j	11508 <_fwalk_reent>

00010f18 <__sinit>:
   10f18:	03852783          	lw	a5,56(a0)
   10f1c:	00078463          	beqz	a5,10f24 <__sinit+0xc>
   10f20:	00008067          	ret
   10f24:	cc1ff06f          	j	10be4 <__sinit.part.0>

00010f28 <__sfp_lock_acquire>:
   10f28:	00008067          	ret

00010f2c <__sfp_lock_release>:
   10f2c:	00008067          	ret

00010f30 <__sinit_lock_acquire>:
   10f30:	00008067          	ret

00010f34 <__sinit_lock_release>:
   10f34:	00008067          	ret

00010f38 <__fp_lock_all>:
   10f38:	00000597          	auipc	a1,0x0
   10f3c:	c9058593          	addi	a1,a1,-880 # 10bc8 <__fp_lock>
   10f40:	0381a503          	lw	a0,56(gp) # 17ba0 <_impure_ptr>
   10f44:	5200006f          	j	11464 <_fwalk>

00010f48 <__fp_unlock_all>:
   10f48:	00000597          	auipc	a1,0x0
   10f4c:	c9458593          	addi	a1,a1,-876 # 10bdc <__fp_unlock>
   10f50:	0381a503          	lw	a0,56(gp) # 17ba0 <_impure_ptr>
   10f54:	5100006f          	j	11464 <_fwalk>

00010f58 <__libc_fini_array>:
   10f58:	ff010113          	addi	sp,sp,-16
   10f5c:	00812423          	sw	s0,8(sp)
   10f60:	00006797          	auipc	a5,0x6
   10f64:	40078793          	addi	a5,a5,1024 # 17360 <__do_global_dtors_aux_fini_array_entry>
   10f68:	00006417          	auipc	s0,0x6
   10f6c:	3fc40413          	addi	s0,s0,1020 # 17364 <__fini_array_end>
   10f70:	40f40433          	sub	s0,s0,a5
   10f74:	00912223          	sw	s1,4(sp)
   10f78:	00112623          	sw	ra,12(sp)
   10f7c:	40245493          	srai	s1,s0,0x2
   10f80:	02048063          	beqz	s1,10fa0 <__libc_fini_array+0x48>
   10f84:	ffc40413          	addi	s0,s0,-4
   10f88:	00f40433          	add	s0,s0,a5
   10f8c:	00042783          	lw	a5,0(s0)
   10f90:	fff48493          	addi	s1,s1,-1
   10f94:	ffc40413          	addi	s0,s0,-4
   10f98:	000780e7          	jalr	a5
   10f9c:	fe0498e3          	bnez	s1,10f8c <__libc_fini_array+0x34>
   10fa0:	00c12083          	lw	ra,12(sp)
   10fa4:	00812403          	lw	s0,8(sp)
   10fa8:	00412483          	lw	s1,4(sp)
   10fac:	01010113          	addi	sp,sp,16
   10fb0:	00008067          	ret

00010fb4 <__sfvwrite_r>:
   10fb4:	00862783          	lw	a5,8(a2)
   10fb8:	32078063          	beqz	a5,112d8 <__sfvwrite_r+0x324>
   10fbc:	00c5d683          	lhu	a3,12(a1)
   10fc0:	fd010113          	addi	sp,sp,-48
   10fc4:	02812423          	sw	s0,40(sp)
   10fc8:	01412c23          	sw	s4,24(sp)
   10fcc:	01712623          	sw	s7,12(sp)
   10fd0:	02112623          	sw	ra,44(sp)
   10fd4:	02912223          	sw	s1,36(sp)
   10fd8:	03212023          	sw	s2,32(sp)
   10fdc:	01312e23          	sw	s3,28(sp)
   10fe0:	01512a23          	sw	s5,20(sp)
   10fe4:	01612823          	sw	s6,16(sp)
   10fe8:	01812423          	sw	s8,8(sp)
   10fec:	01912223          	sw	s9,4(sp)
   10ff0:	01a12023          	sw	s10,0(sp)
   10ff4:	0086f793          	andi	a5,a3,8
   10ff8:	00060b93          	mv	s7,a2
   10ffc:	00050a13          	mv	s4,a0
   11000:	00058413          	mv	s0,a1
   11004:	08078663          	beqz	a5,11090 <__sfvwrite_r+0xdc>
   11008:	0105a783          	lw	a5,16(a1)
   1100c:	08078263          	beqz	a5,11090 <__sfvwrite_r+0xdc>
   11010:	0026f793          	andi	a5,a3,2
   11014:	000ba483          	lw	s1,0(s7)
   11018:	08078c63          	beqz	a5,110b0 <__sfvwrite_r+0xfc>
   1101c:	02442783          	lw	a5,36(s0)
   11020:	01c42583          	lw	a1,28(s0)
   11024:	80000ab7          	lui	s5,0x80000
   11028:	00000993          	li	s3,0
   1102c:	00000913          	li	s2,0
   11030:	c00aca93          	xori	s5,s5,-1024
   11034:	00098613          	mv	a2,s3
   11038:	000a0513          	mv	a0,s4
   1103c:	04090263          	beqz	s2,11080 <__sfvwrite_r+0xcc>
   11040:	00090693          	mv	a3,s2
   11044:	012af463          	bgeu	s5,s2,1104c <__sfvwrite_r+0x98>
   11048:	000a8693          	mv	a3,s5
   1104c:	000780e7          	jalr	a5
   11050:	26a05a63          	blez	a0,112c4 <__sfvwrite_r+0x310>
   11054:	008ba783          	lw	a5,8(s7)
   11058:	00a989b3          	add	s3,s3,a0
   1105c:	40a90933          	sub	s2,s2,a0
   11060:	40a787b3          	sub	a5,a5,a0
   11064:	00fba423          	sw	a5,8(s7)
   11068:	20078863          	beqz	a5,11278 <__sfvwrite_r+0x2c4>
   1106c:	02442783          	lw	a5,36(s0)
   11070:	01c42583          	lw	a1,28(s0)
   11074:	00098613          	mv	a2,s3
   11078:	000a0513          	mv	a0,s4
   1107c:	fc0912e3          	bnez	s2,11040 <__sfvwrite_r+0x8c>
   11080:	0004a983          	lw	s3,0(s1)
   11084:	0044a903          	lw	s2,4(s1)
   11088:	00848493          	addi	s1,s1,8
   1108c:	fa9ff06f          	j	11034 <__sfvwrite_r+0x80>
   11090:	00040593          	mv	a1,s0
   11094:	000a0513          	mv	a0,s4
   11098:	740010ef          	jal	ra,127d8 <__swsetup_r>
   1109c:	3c051063          	bnez	a0,1145c <__sfvwrite_r+0x4a8>
   110a0:	00c45683          	lhu	a3,12(s0)
   110a4:	000ba483          	lw	s1,0(s7)
   110a8:	0026f793          	andi	a5,a3,2
   110ac:	f60798e3          	bnez	a5,1101c <__sfvwrite_r+0x68>
   110b0:	0016f793          	andi	a5,a3,1
   110b4:	12079e63          	bnez	a5,111f0 <__sfvwrite_r+0x23c>
   110b8:	00042783          	lw	a5,0(s0)
   110bc:	00842703          	lw	a4,8(s0)
   110c0:	80000ab7          	lui	s5,0x80000
   110c4:	ffeacb13          	xori	s6,s5,-2
   110c8:	00000c13          	li	s8,0
   110cc:	00000993          	li	s3,0
   110d0:	fffaca93          	not	s5,s5
   110d4:	00078513          	mv	a0,a5
   110d8:	00070c93          	mv	s9,a4
   110dc:	10098263          	beqz	s3,111e0 <__sfvwrite_r+0x22c>
   110e0:	2006f613          	andi	a2,a3,512
   110e4:	24060e63          	beqz	a2,11340 <__sfvwrite_r+0x38c>
   110e8:	00070d13          	mv	s10,a4
   110ec:	2ee9e663          	bltu	s3,a4,113d8 <__sfvwrite_r+0x424>
   110f0:	4806f713          	andi	a4,a3,1152
   110f4:	08070a63          	beqz	a4,11188 <__sfvwrite_r+0x1d4>
   110f8:	01442603          	lw	a2,20(s0)
   110fc:	01042583          	lw	a1,16(s0)
   11100:	00161713          	slli	a4,a2,0x1
   11104:	00c70733          	add	a4,a4,a2
   11108:	40b78933          	sub	s2,a5,a1
   1110c:	01f75c93          	srli	s9,a4,0x1f
   11110:	00ec8cb3          	add	s9,s9,a4
   11114:	00190793          	addi	a5,s2,1
   11118:	401cdc93          	srai	s9,s9,0x1
   1111c:	013787b3          	add	a5,a5,s3
   11120:	000c8613          	mv	a2,s9
   11124:	00fcf663          	bgeu	s9,a5,11130 <__sfvwrite_r+0x17c>
   11128:	00078c93          	mv	s9,a5
   1112c:	00078613          	mv	a2,a5
   11130:	4006f693          	andi	a3,a3,1024
   11134:	2c068e63          	beqz	a3,11410 <__sfvwrite_r+0x45c>
   11138:	00060593          	mv	a1,a2
   1113c:	000a0513          	mv	a0,s4
   11140:	47c000ef          	jal	ra,115bc <_malloc_r>
   11144:	00050d13          	mv	s10,a0
   11148:	30050263          	beqz	a0,1144c <__sfvwrite_r+0x498>
   1114c:	01042583          	lw	a1,16(s0)
   11150:	00090613          	mv	a2,s2
   11154:	4d5000ef          	jal	ra,11e28 <memcpy>
   11158:	00c45783          	lhu	a5,12(s0)
   1115c:	b7f7f793          	andi	a5,a5,-1153
   11160:	0807e793          	ori	a5,a5,128
   11164:	00f41623          	sh	a5,12(s0)
   11168:	012d0533          	add	a0,s10,s2
   1116c:	412c87b3          	sub	a5,s9,s2
   11170:	01a42823          	sw	s10,16(s0)
   11174:	01942a23          	sw	s9,20(s0)
   11178:	00a42023          	sw	a0,0(s0)
   1117c:	00098c93          	mv	s9,s3
   11180:	00f42423          	sw	a5,8(s0)
   11184:	00098d13          	mv	s10,s3
   11188:	000d0613          	mv	a2,s10
   1118c:	000c0593          	mv	a1,s8
   11190:	5c1000ef          	jal	ra,11f50 <memmove>
   11194:	00842703          	lw	a4,8(s0)
   11198:	00042783          	lw	a5,0(s0)
   1119c:	00098913          	mv	s2,s3
   111a0:	41970733          	sub	a4,a4,s9
   111a4:	01a787b3          	add	a5,a5,s10
   111a8:	00e42423          	sw	a4,8(s0)
   111ac:	00f42023          	sw	a5,0(s0)
   111b0:	00000993          	li	s3,0
   111b4:	008ba783          	lw	a5,8(s7)
   111b8:	012c0c33          	add	s8,s8,s2
   111bc:	412787b3          	sub	a5,a5,s2
   111c0:	00fba423          	sw	a5,8(s7)
   111c4:	0a078a63          	beqz	a5,11278 <__sfvwrite_r+0x2c4>
   111c8:	00042783          	lw	a5,0(s0)
   111cc:	00842703          	lw	a4,8(s0)
   111d0:	00c45683          	lhu	a3,12(s0)
   111d4:	00078513          	mv	a0,a5
   111d8:	00070c93          	mv	s9,a4
   111dc:	f00992e3          	bnez	s3,110e0 <__sfvwrite_r+0x12c>
   111e0:	0004ac03          	lw	s8,0(s1)
   111e4:	0044a983          	lw	s3,4(s1)
   111e8:	00848493          	addi	s1,s1,8
   111ec:	ee9ff06f          	j	110d4 <__sfvwrite_r+0x120>
   111f0:	00000a93          	li	s5,0
   111f4:	00000513          	li	a0,0
   111f8:	00000c13          	li	s8,0
   111fc:	00000993          	li	s3,0
   11200:	0e098063          	beqz	s3,112e0 <__sfvwrite_r+0x32c>
   11204:	0e050863          	beqz	a0,112f4 <__sfvwrite_r+0x340>
   11208:	000a8793          	mv	a5,s5
   1120c:	00098b13          	mv	s6,s3
   11210:	0137f463          	bgeu	a5,s3,11218 <__sfvwrite_r+0x264>
   11214:	00078b13          	mv	s6,a5
   11218:	00042503          	lw	a0,0(s0)
   1121c:	01042783          	lw	a5,16(s0)
   11220:	00842903          	lw	s2,8(s0)
   11224:	01442683          	lw	a3,20(s0)
   11228:	00a7f663          	bgeu	a5,a0,11234 <__sfvwrite_r+0x280>
   1122c:	00d90933          	add	s2,s2,a3
   11230:	0f694263          	blt	s2,s6,11314 <__sfvwrite_r+0x360>
   11234:	1adb4863          	blt	s6,a3,113e4 <__sfvwrite_r+0x430>
   11238:	02442783          	lw	a5,36(s0)
   1123c:	01c42583          	lw	a1,28(s0)
   11240:	000c0613          	mv	a2,s8
   11244:	000a0513          	mv	a0,s4
   11248:	000780e7          	jalr	a5
   1124c:	00050913          	mv	s2,a0
   11250:	06a05a63          	blez	a0,112c4 <__sfvwrite_r+0x310>
   11254:	412a8ab3          	sub	s5,s5,s2
   11258:	00100513          	li	a0,1
   1125c:	040a8c63          	beqz	s5,112b4 <__sfvwrite_r+0x300>
   11260:	008ba783          	lw	a5,8(s7)
   11264:	012c0c33          	add	s8,s8,s2
   11268:	412989b3          	sub	s3,s3,s2
   1126c:	412787b3          	sub	a5,a5,s2
   11270:	00fba423          	sw	a5,8(s7)
   11274:	f80796e3          	bnez	a5,11200 <__sfvwrite_r+0x24c>
   11278:	00000513          	li	a0,0
   1127c:	02c12083          	lw	ra,44(sp)
   11280:	02812403          	lw	s0,40(sp)
   11284:	02412483          	lw	s1,36(sp)
   11288:	02012903          	lw	s2,32(sp)
   1128c:	01c12983          	lw	s3,28(sp)
   11290:	01812a03          	lw	s4,24(sp)
   11294:	01412a83          	lw	s5,20(sp)
   11298:	01012b03          	lw	s6,16(sp)
   1129c:	00c12b83          	lw	s7,12(sp)
   112a0:	00812c03          	lw	s8,8(sp)
   112a4:	00412c83          	lw	s9,4(sp)
   112a8:	00012d03          	lw	s10,0(sp)
   112ac:	03010113          	addi	sp,sp,48
   112b0:	00008067          	ret
   112b4:	00040593          	mv	a1,s0
   112b8:	000a0513          	mv	a0,s4
   112bc:	2ed010ef          	jal	ra,12da8 <_fflush_r>
   112c0:	fa0500e3          	beqz	a0,11260 <__sfvwrite_r+0x2ac>
   112c4:	00c41783          	lh	a5,12(s0)
   112c8:	0407e793          	ori	a5,a5,64
   112cc:	00f41623          	sh	a5,12(s0)
   112d0:	fff00513          	li	a0,-1
   112d4:	fa9ff06f          	j	1127c <__sfvwrite_r+0x2c8>
   112d8:	00000513          	li	a0,0
   112dc:	00008067          	ret
   112e0:	0044a983          	lw	s3,4(s1)
   112e4:	00048793          	mv	a5,s1
   112e8:	00848493          	addi	s1,s1,8
   112ec:	fe098ae3          	beqz	s3,112e0 <__sfvwrite_r+0x32c>
   112f0:	0007ac03          	lw	s8,0(a5)
   112f4:	00098613          	mv	a2,s3
   112f8:	00a00593          	li	a1,10
   112fc:	000c0513          	mv	a0,s8
   11300:	261000ef          	jal	ra,11d60 <memchr>
   11304:	12050e63          	beqz	a0,11440 <__sfvwrite_r+0x48c>
   11308:	00150513          	addi	a0,a0,1
   1130c:	41850ab3          	sub	s5,a0,s8
   11310:	ef9ff06f          	j	11208 <__sfvwrite_r+0x254>
   11314:	000c0593          	mv	a1,s8
   11318:	00090613          	mv	a2,s2
   1131c:	435000ef          	jal	ra,11f50 <memmove>
   11320:	00042783          	lw	a5,0(s0)
   11324:	00040593          	mv	a1,s0
   11328:	000a0513          	mv	a0,s4
   1132c:	012787b3          	add	a5,a5,s2
   11330:	00f42023          	sw	a5,0(s0)
   11334:	275010ef          	jal	ra,12da8 <_fflush_r>
   11338:	f0050ee3          	beqz	a0,11254 <__sfvwrite_r+0x2a0>
   1133c:	f89ff06f          	j	112c4 <__sfvwrite_r+0x310>
   11340:	01042683          	lw	a3,16(s0)
   11344:	04f6e263          	bltu	a3,a5,11388 <__sfvwrite_r+0x3d4>
   11348:	01442803          	lw	a6,20(s0)
   1134c:	0309ee63          	bltu	s3,a6,11388 <__sfvwrite_r+0x3d4>
   11350:	00098693          	mv	a3,s3
   11354:	013b7463          	bgeu	s6,s3,1135c <__sfvwrite_r+0x3a8>
   11358:	000a8693          	mv	a3,s5
   1135c:	0306c6b3          	div	a3,a3,a6
   11360:	02442783          	lw	a5,36(s0)
   11364:	01c42583          	lw	a1,28(s0)
   11368:	000c0613          	mv	a2,s8
   1136c:	000a0513          	mv	a0,s4
   11370:	030686b3          	mul	a3,a3,a6
   11374:	000780e7          	jalr	a5
   11378:	00050913          	mv	s2,a0
   1137c:	f4a054e3          	blez	a0,112c4 <__sfvwrite_r+0x310>
   11380:	412989b3          	sub	s3,s3,s2
   11384:	e31ff06f          	j	111b4 <__sfvwrite_r+0x200>
   11388:	00070913          	mv	s2,a4
   1138c:	00e9f463          	bgeu	s3,a4,11394 <__sfvwrite_r+0x3e0>
   11390:	00098913          	mv	s2,s3
   11394:	00078513          	mv	a0,a5
   11398:	00090613          	mv	a2,s2
   1139c:	000c0593          	mv	a1,s8
   113a0:	3b1000ef          	jal	ra,11f50 <memmove>
   113a4:	00842703          	lw	a4,8(s0)
   113a8:	00042783          	lw	a5,0(s0)
   113ac:	41270733          	sub	a4,a4,s2
   113b0:	012787b3          	add	a5,a5,s2
   113b4:	00e42423          	sw	a4,8(s0)
   113b8:	00f42023          	sw	a5,0(s0)
   113bc:	fc0712e3          	bnez	a4,11380 <__sfvwrite_r+0x3cc>
   113c0:	00040593          	mv	a1,s0
   113c4:	000a0513          	mv	a0,s4
   113c8:	1e1010ef          	jal	ra,12da8 <_fflush_r>
   113cc:	ee051ce3          	bnez	a0,112c4 <__sfvwrite_r+0x310>
   113d0:	412989b3          	sub	s3,s3,s2
   113d4:	de1ff06f          	j	111b4 <__sfvwrite_r+0x200>
   113d8:	00098c93          	mv	s9,s3
   113dc:	00098d13          	mv	s10,s3
   113e0:	da9ff06f          	j	11188 <__sfvwrite_r+0x1d4>
   113e4:	000b0613          	mv	a2,s6
   113e8:	000c0593          	mv	a1,s8
   113ec:	365000ef          	jal	ra,11f50 <memmove>
   113f0:	00842703          	lw	a4,8(s0)
   113f4:	00042783          	lw	a5,0(s0)
   113f8:	000b0913          	mv	s2,s6
   113fc:	41670733          	sub	a4,a4,s6
   11400:	016787b3          	add	a5,a5,s6
   11404:	00e42423          	sw	a4,8(s0)
   11408:	00f42023          	sw	a5,0(s0)
   1140c:	e49ff06f          	j	11254 <__sfvwrite_r+0x2a0>
   11410:	000a0513          	mv	a0,s4
   11414:	465000ef          	jal	ra,12078 <_realloc_r>
   11418:	00050d13          	mv	s10,a0
   1141c:	d40516e3          	bnez	a0,11168 <__sfvwrite_r+0x1b4>
   11420:	01042583          	lw	a1,16(s0)
   11424:	000a0513          	mv	a0,s4
   11428:	38d010ef          	jal	ra,12fb4 <_free_r>
   1142c:	00c41783          	lh	a5,12(s0)
   11430:	00c00713          	li	a4,12
   11434:	00ea2023          	sw	a4,0(s4)
   11438:	f7f7f793          	andi	a5,a5,-129
   1143c:	e8dff06f          	j	112c8 <__sfvwrite_r+0x314>
   11440:	00198793          	addi	a5,s3,1
   11444:	00078a93          	mv	s5,a5
   11448:	dc5ff06f          	j	1120c <__sfvwrite_r+0x258>
   1144c:	00c00713          	li	a4,12
   11450:	00c41783          	lh	a5,12(s0)
   11454:	00ea2023          	sw	a4,0(s4)
   11458:	e71ff06f          	j	112c8 <__sfvwrite_r+0x314>
   1145c:	fff00513          	li	a0,-1
   11460:	e1dff06f          	j	1127c <__sfvwrite_r+0x2c8>

00011464 <_fwalk>:
   11464:	fe010113          	addi	sp,sp,-32
   11468:	01212823          	sw	s2,16(sp)
   1146c:	01312623          	sw	s3,12(sp)
   11470:	01412423          	sw	s4,8(sp)
   11474:	01512223          	sw	s5,4(sp)
   11478:	01612023          	sw	s6,0(sp)
   1147c:	00112e23          	sw	ra,28(sp)
   11480:	00812c23          	sw	s0,24(sp)
   11484:	00912a23          	sw	s1,20(sp)
   11488:	00058b13          	mv	s6,a1
   1148c:	2e050a93          	addi	s5,a0,736
   11490:	00000a13          	li	s4,0
   11494:	00100993          	li	s3,1
   11498:	fff00913          	li	s2,-1
   1149c:	004aa483          	lw	s1,4(s5) # 80000004 <__BSS_END__+0x7ffe8400>
   114a0:	008aa403          	lw	s0,8(s5)
   114a4:	fff48493          	addi	s1,s1,-1
   114a8:	0204c663          	bltz	s1,114d4 <_fwalk+0x70>
   114ac:	00c45783          	lhu	a5,12(s0)
   114b0:	fff48493          	addi	s1,s1,-1
   114b4:	00f9fc63          	bgeu	s3,a5,114cc <_fwalk+0x68>
   114b8:	00e41783          	lh	a5,14(s0)
   114bc:	00040513          	mv	a0,s0
   114c0:	01278663          	beq	a5,s2,114cc <_fwalk+0x68>
   114c4:	000b00e7          	jalr	s6
   114c8:	00aa6a33          	or	s4,s4,a0
   114cc:	06840413          	addi	s0,s0,104
   114d0:	fd249ee3          	bne	s1,s2,114ac <_fwalk+0x48>
   114d4:	000aaa83          	lw	s5,0(s5)
   114d8:	fc0a92e3          	bnez	s5,1149c <_fwalk+0x38>
   114dc:	01c12083          	lw	ra,28(sp)
   114e0:	01812403          	lw	s0,24(sp)
   114e4:	01412483          	lw	s1,20(sp)
   114e8:	01012903          	lw	s2,16(sp)
   114ec:	00c12983          	lw	s3,12(sp)
   114f0:	00412a83          	lw	s5,4(sp)
   114f4:	00012b03          	lw	s6,0(sp)
   114f8:	000a0513          	mv	a0,s4
   114fc:	00812a03          	lw	s4,8(sp)
   11500:	02010113          	addi	sp,sp,32
   11504:	00008067          	ret

00011508 <_fwalk_reent>:
   11508:	fd010113          	addi	sp,sp,-48
   1150c:	03212023          	sw	s2,32(sp)
   11510:	01312e23          	sw	s3,28(sp)
   11514:	01412c23          	sw	s4,24(sp)
   11518:	01512a23          	sw	s5,20(sp)
   1151c:	01612823          	sw	s6,16(sp)
   11520:	01712623          	sw	s7,12(sp)
   11524:	02112623          	sw	ra,44(sp)
   11528:	02812423          	sw	s0,40(sp)
   1152c:	02912223          	sw	s1,36(sp)
   11530:	00050a93          	mv	s5,a0
   11534:	00058b93          	mv	s7,a1
   11538:	2e050b13          	addi	s6,a0,736
   1153c:	00000a13          	li	s4,0
   11540:	00100993          	li	s3,1
   11544:	fff00913          	li	s2,-1
   11548:	004b2483          	lw	s1,4(s6)
   1154c:	008b2403          	lw	s0,8(s6)
   11550:	fff48493          	addi	s1,s1,-1
   11554:	0204c863          	bltz	s1,11584 <_fwalk_reent+0x7c>
   11558:	00c45783          	lhu	a5,12(s0)
   1155c:	fff48493          	addi	s1,s1,-1
   11560:	00f9fe63          	bgeu	s3,a5,1157c <_fwalk_reent+0x74>
   11564:	00e41783          	lh	a5,14(s0)
   11568:	00040593          	mv	a1,s0
   1156c:	000a8513          	mv	a0,s5
   11570:	01278663          	beq	a5,s2,1157c <_fwalk_reent+0x74>
   11574:	000b80e7          	jalr	s7
   11578:	00aa6a33          	or	s4,s4,a0
   1157c:	06840413          	addi	s0,s0,104
   11580:	fd249ce3          	bne	s1,s2,11558 <_fwalk_reent+0x50>
   11584:	000b2b03          	lw	s6,0(s6)
   11588:	fc0b10e3          	bnez	s6,11548 <_fwalk_reent+0x40>
   1158c:	02c12083          	lw	ra,44(sp)
   11590:	02812403          	lw	s0,40(sp)
   11594:	02412483          	lw	s1,36(sp)
   11598:	02012903          	lw	s2,32(sp)
   1159c:	01c12983          	lw	s3,28(sp)
   115a0:	01412a83          	lw	s5,20(sp)
   115a4:	01012b03          	lw	s6,16(sp)
   115a8:	00c12b83          	lw	s7,12(sp)
   115ac:	000a0513          	mv	a0,s4
   115b0:	01812a03          	lw	s4,24(sp)
   115b4:	03010113          	addi	sp,sp,48
   115b8:	00008067          	ret

000115bc <_malloc_r>:
   115bc:	fd010113          	addi	sp,sp,-48
   115c0:	03212023          	sw	s2,32(sp)
   115c4:	02112623          	sw	ra,44(sp)
   115c8:	02812423          	sw	s0,40(sp)
   115cc:	02912223          	sw	s1,36(sp)
   115d0:	01312e23          	sw	s3,28(sp)
   115d4:	01412c23          	sw	s4,24(sp)
   115d8:	01512a23          	sw	s5,20(sp)
   115dc:	01612823          	sw	s6,16(sp)
   115e0:	01712623          	sw	s7,12(sp)
   115e4:	01812423          	sw	s8,8(sp)
   115e8:	01912223          	sw	s9,4(sp)
   115ec:	00b58793          	addi	a5,a1,11
   115f0:	01600713          	li	a4,22
   115f4:	00050913          	mv	s2,a0
   115f8:	06f76463          	bltu	a4,a5,11660 <_malloc_r+0xa4>
   115fc:	01000793          	li	a5,16
   11600:	1eb7e263          	bltu	a5,a1,117e4 <_malloc_r+0x228>
   11604:	26d000ef          	jal	ra,12070 <__malloc_lock>
   11608:	01000493          	li	s1,16
   1160c:	01800793          	li	a5,24
   11610:	00200613          	li	a2,2
   11614:	c2818993          	addi	s3,gp,-984 # 17790 <__malloc_av_>
   11618:	00f987b3          	add	a5,s3,a5
   1161c:	0047a403          	lw	s0,4(a5)
   11620:	ff878713          	addi	a4,a5,-8
   11624:	20e40863          	beq	s0,a4,11834 <_malloc_r+0x278>
   11628:	00442783          	lw	a5,4(s0)
   1162c:	00c42683          	lw	a3,12(s0)
   11630:	00842603          	lw	a2,8(s0)
   11634:	ffc7f793          	andi	a5,a5,-4
   11638:	00f407b3          	add	a5,s0,a5
   1163c:	0047a703          	lw	a4,4(a5)
   11640:	00d62623          	sw	a3,12(a2)
   11644:	00c6a423          	sw	a2,8(a3)
   11648:	00176713          	ori	a4,a4,1
   1164c:	00090513          	mv	a0,s2
   11650:	00e7a223          	sw	a4,4(a5)
   11654:	221000ef          	jal	ra,12074 <__malloc_unlock>
   11658:	00840513          	addi	a0,s0,8
   1165c:	1940006f          	j	117f0 <_malloc_r+0x234>
   11660:	ff87f493          	andi	s1,a5,-8
   11664:	1807c063          	bltz	a5,117e4 <_malloc_r+0x228>
   11668:	16b4ee63          	bltu	s1,a1,117e4 <_malloc_r+0x228>
   1166c:	205000ef          	jal	ra,12070 <__malloc_lock>
   11670:	1f700793          	li	a5,503
   11674:	4697f063          	bgeu	a5,s1,11ad4 <_malloc_r+0x518>
   11678:	0094d793          	srli	a5,s1,0x9
   1167c:	1a078463          	beqz	a5,11824 <_malloc_r+0x268>
   11680:	00400713          	li	a4,4
   11684:	3cf76663          	bltu	a4,a5,11a50 <_malloc_r+0x494>
   11688:	0064d793          	srli	a5,s1,0x6
   1168c:	03978613          	addi	a2,a5,57
   11690:	03878513          	addi	a0,a5,56
   11694:	00361693          	slli	a3,a2,0x3
   11698:	c2818993          	addi	s3,gp,-984 # 17790 <__malloc_av_>
   1169c:	00d986b3          	add	a3,s3,a3
   116a0:	0046a403          	lw	s0,4(a3)
   116a4:	ff868693          	addi	a3,a3,-8
   116a8:	02868663          	beq	a3,s0,116d4 <_malloc_r+0x118>
   116ac:	00f00593          	li	a1,15
   116b0:	0100006f          	j	116c0 <_malloc_r+0x104>
   116b4:	32075863          	bgez	a4,119e4 <_malloc_r+0x428>
   116b8:	00c42403          	lw	s0,12(s0)
   116bc:	00868c63          	beq	a3,s0,116d4 <_malloc_r+0x118>
   116c0:	00442783          	lw	a5,4(s0)
   116c4:	ffc7f793          	andi	a5,a5,-4
   116c8:	40978733          	sub	a4,a5,s1
   116cc:	fee5d4e3          	bge	a1,a4,116b4 <_malloc_r+0xf8>
   116d0:	00050613          	mv	a2,a0
   116d4:	0109a403          	lw	s0,16(s3)
   116d8:	c3018893          	addi	a7,gp,-976 # 17798 <__malloc_av_+0x8>
   116dc:	17140863          	beq	s0,a7,1184c <_malloc_r+0x290>
   116e0:	00442583          	lw	a1,4(s0)
   116e4:	00f00713          	li	a4,15
   116e8:	ffc5f593          	andi	a1,a1,-4
   116ec:	409587b3          	sub	a5,a1,s1
   116f0:	40f74863          	blt	a4,a5,11b00 <_malloc_r+0x544>
   116f4:	0119aa23          	sw	a7,20(s3)
   116f8:	0119a823          	sw	a7,16(s3)
   116fc:	3e07d263          	bgez	a5,11ae0 <_malloc_r+0x524>
   11700:	1ff00793          	li	a5,511
   11704:	2eb7e663          	bltu	a5,a1,119f0 <_malloc_r+0x434>
   11708:	ff85f793          	andi	a5,a1,-8
   1170c:	00878793          	addi	a5,a5,8
   11710:	0049a503          	lw	a0,4(s3)
   11714:	00f987b3          	add	a5,s3,a5
   11718:	0007a683          	lw	a3,0(a5)
   1171c:	0055d593          	srli	a1,a1,0x5
   11720:	00100713          	li	a4,1
   11724:	00b71733          	sll	a4,a4,a1
   11728:	00a76733          	or	a4,a4,a0
   1172c:	ff878593          	addi	a1,a5,-8
   11730:	00b42623          	sw	a1,12(s0)
   11734:	00d42423          	sw	a3,8(s0)
   11738:	00e9a223          	sw	a4,4(s3)
   1173c:	0087a023          	sw	s0,0(a5)
   11740:	0086a623          	sw	s0,12(a3)
   11744:	40265793          	srai	a5,a2,0x2
   11748:	00100593          	li	a1,1
   1174c:	00f595b3          	sll	a1,a1,a5
   11750:	10b76863          	bltu	a4,a1,11860 <_malloc_r+0x2a4>
   11754:	00e5f7b3          	and	a5,a1,a4
   11758:	02079463          	bnez	a5,11780 <_malloc_r+0x1c4>
   1175c:	00159593          	slli	a1,a1,0x1
   11760:	ffc67613          	andi	a2,a2,-4
   11764:	00e5f7b3          	and	a5,a1,a4
   11768:	00460613          	addi	a2,a2,4
   1176c:	00079a63          	bnez	a5,11780 <_malloc_r+0x1c4>
   11770:	00159593          	slli	a1,a1,0x1
   11774:	00e5f7b3          	and	a5,a1,a4
   11778:	00460613          	addi	a2,a2,4
   1177c:	fe078ae3          	beqz	a5,11770 <_malloc_r+0x1b4>
   11780:	00f00813          	li	a6,15
   11784:	00361313          	slli	t1,a2,0x3
   11788:	00698333          	add	t1,s3,t1
   1178c:	00030513          	mv	a0,t1
   11790:	00c52783          	lw	a5,12(a0)
   11794:	00060e13          	mv	t3,a2
   11798:	2cf50e63          	beq	a0,a5,11a74 <_malloc_r+0x4b8>
   1179c:	0047a703          	lw	a4,4(a5)
   117a0:	00078413          	mv	s0,a5
   117a4:	00c7a783          	lw	a5,12(a5)
   117a8:	ffc77713          	andi	a4,a4,-4
   117ac:	409706b3          	sub	a3,a4,s1
   117b0:	2cd84e63          	blt	a6,a3,11a8c <_malloc_r+0x4d0>
   117b4:	fe06c2e3          	bltz	a3,11798 <_malloc_r+0x1dc>
   117b8:	00e40733          	add	a4,s0,a4
   117bc:	00472683          	lw	a3,4(a4)
   117c0:	00842603          	lw	a2,8(s0)
   117c4:	00090513          	mv	a0,s2
   117c8:	0016e693          	ori	a3,a3,1
   117cc:	00d72223          	sw	a3,4(a4)
   117d0:	00f62623          	sw	a5,12(a2)
   117d4:	00c7a423          	sw	a2,8(a5)
   117d8:	09d000ef          	jal	ra,12074 <__malloc_unlock>
   117dc:	00840513          	addi	a0,s0,8
   117e0:	0100006f          	j	117f0 <_malloc_r+0x234>
   117e4:	00c00793          	li	a5,12
   117e8:	00f92023          	sw	a5,0(s2)
   117ec:	00000513          	li	a0,0
   117f0:	02c12083          	lw	ra,44(sp)
   117f4:	02812403          	lw	s0,40(sp)
   117f8:	02412483          	lw	s1,36(sp)
   117fc:	02012903          	lw	s2,32(sp)
   11800:	01c12983          	lw	s3,28(sp)
   11804:	01812a03          	lw	s4,24(sp)
   11808:	01412a83          	lw	s5,20(sp)
   1180c:	01012b03          	lw	s6,16(sp)
   11810:	00c12b83          	lw	s7,12(sp)
   11814:	00812c03          	lw	s8,8(sp)
   11818:	00412c83          	lw	s9,4(sp)
   1181c:	03010113          	addi	sp,sp,48
   11820:	00008067          	ret
   11824:	20000693          	li	a3,512
   11828:	04000613          	li	a2,64
   1182c:	03f00513          	li	a0,63
   11830:	e69ff06f          	j	11698 <_malloc_r+0xdc>
   11834:	00c7a403          	lw	s0,12(a5)
   11838:	00260613          	addi	a2,a2,2
   1183c:	de8796e3          	bne	a5,s0,11628 <_malloc_r+0x6c>
   11840:	0109a403          	lw	s0,16(s3)
   11844:	c3018893          	addi	a7,gp,-976 # 17798 <__malloc_av_+0x8>
   11848:	e9141ce3          	bne	s0,a7,116e0 <_malloc_r+0x124>
   1184c:	0049a703          	lw	a4,4(s3)
   11850:	40265793          	srai	a5,a2,0x2
   11854:	00100593          	li	a1,1
   11858:	00f595b3          	sll	a1,a1,a5
   1185c:	eeb77ce3          	bgeu	a4,a1,11754 <_malloc_r+0x198>
   11860:	0089a403          	lw	s0,8(s3)
   11864:	00442b03          	lw	s6,4(s0)
   11868:	ffcb7b13          	andi	s6,s6,-4
   1186c:	009b6863          	bltu	s6,s1,1187c <_malloc_r+0x2c0>
   11870:	409b07b3          	sub	a5,s6,s1
   11874:	00f00713          	li	a4,15
   11878:	14f74263          	blt	a4,a5,119bc <_malloc_r+0x400>
   1187c:	03c18c93          	addi	s9,gp,60 # 17ba4 <__malloc_sbrk_base>
   11880:	000ca703          	lw	a4,0(s9)
   11884:	04c1aa83          	lw	s5,76(gp) # 17bb4 <__malloc_top_pad>
   11888:	fff00793          	li	a5,-1
   1188c:	01640a33          	add	s4,s0,s6
   11890:	01548ab3          	add	s5,s1,s5
   11894:	34f70863          	beq	a4,a5,11be4 <_malloc_r+0x628>
   11898:	000017b7          	lui	a5,0x1
   1189c:	00f78793          	addi	a5,a5,15 # 100f <main-0xf065>
   118a0:	00fa8ab3          	add	s5,s5,a5
   118a4:	fffff7b7          	lui	a5,0xfffff
   118a8:	00fafab3          	and	s5,s5,a5
   118ac:	000a8593          	mv	a1,s5
   118b0:	00090513          	mv	a0,s2
   118b4:	51d000ef          	jal	ra,125d0 <_sbrk_r>
   118b8:	fff00793          	li	a5,-1
   118bc:	00050b93          	mv	s7,a0
   118c0:	28f50a63          	beq	a0,a5,11b54 <_malloc_r+0x598>
   118c4:	29456663          	bltu	a0,s4,11b50 <_malloc_r+0x594>
   118c8:	07418c13          	addi	s8,gp,116 # 17bdc <__malloc_current_mallinfo>
   118cc:	000c2583          	lw	a1,0(s8)
   118d0:	00ba85b3          	add	a1,s5,a1
   118d4:	00bc2023          	sw	a1,0(s8)
   118d8:	00058793          	mv	a5,a1
   118dc:	3aaa0263          	beq	s4,a0,11c80 <_malloc_r+0x6c4>
   118e0:	000ca683          	lw	a3,0(s9)
   118e4:	fff00713          	li	a4,-1
   118e8:	3ae68a63          	beq	a3,a4,11c9c <_malloc_r+0x6e0>
   118ec:	414b8a33          	sub	s4,s7,s4
   118f0:	00fa07b3          	add	a5,s4,a5
   118f4:	00fc2023          	sw	a5,0(s8)
   118f8:	007bfc93          	andi	s9,s7,7
   118fc:	300c8663          	beqz	s9,11c08 <_malloc_r+0x64c>
   11900:	000017b7          	lui	a5,0x1
   11904:	419b8bb3          	sub	s7,s7,s9
   11908:	00878593          	addi	a1,a5,8 # 1008 <main-0xf06c>
   1190c:	008b8b93          	addi	s7,s7,8
   11910:	419585b3          	sub	a1,a1,s9
   11914:	015b8ab3          	add	s5,s7,s5
   11918:	fff78793          	addi	a5,a5,-1
   1191c:	415585b3          	sub	a1,a1,s5
   11920:	00f5fa33          	and	s4,a1,a5
   11924:	000a0593          	mv	a1,s4
   11928:	00090513          	mv	a0,s2
   1192c:	4a5000ef          	jal	ra,125d0 <_sbrk_r>
   11930:	fff00793          	li	a5,-1
   11934:	3af50e63          	beq	a0,a5,11cf0 <_malloc_r+0x734>
   11938:	41750533          	sub	a0,a0,s7
   1193c:	01450ab3          	add	s5,a0,s4
   11940:	000c2783          	lw	a5,0(s8)
   11944:	0179a423          	sw	s7,8(s3)
   11948:	001aea93          	ori	s5,s5,1
   1194c:	00fa05b3          	add	a1,s4,a5
   11950:	00bc2023          	sw	a1,0(s8)
   11954:	015ba223          	sw	s5,4(s7)
   11958:	35340663          	beq	s0,s3,11ca4 <_malloc_r+0x6e8>
   1195c:	00f00693          	li	a3,15
   11960:	3566f663          	bgeu	a3,s6,11cac <_malloc_r+0x6f0>
   11964:	00442703          	lw	a4,4(s0)
   11968:	ff4b0793          	addi	a5,s6,-12
   1196c:	ff87f793          	andi	a5,a5,-8
   11970:	00177713          	andi	a4,a4,1
   11974:	00f76733          	or	a4,a4,a5
   11978:	00e42223          	sw	a4,4(s0)
   1197c:	00500613          	li	a2,5
   11980:	00f40733          	add	a4,s0,a5
   11984:	00c72223          	sw	a2,4(a4)
   11988:	00c72423          	sw	a2,8(a4)
   1198c:	36f6ec63          	bltu	a3,a5,11d04 <_malloc_r+0x748>
   11990:	004baa83          	lw	s5,4(s7)
   11994:	000b8413          	mv	s0,s7
   11998:	04818793          	addi	a5,gp,72 # 17bb0 <__malloc_max_sbrked_mem>
   1199c:	0007a703          	lw	a4,0(a5)
   119a0:	00b77463          	bgeu	a4,a1,119a8 <_malloc_r+0x3ec>
   119a4:	00b7a023          	sw	a1,0(a5)
   119a8:	04418793          	addi	a5,gp,68 # 17bac <__malloc_max_total_mem>
   119ac:	0007a703          	lw	a4,0(a5)
   119b0:	1ab77663          	bgeu	a4,a1,11b5c <_malloc_r+0x5a0>
   119b4:	00b7a023          	sw	a1,0(a5)
   119b8:	1a40006f          	j	11b5c <_malloc_r+0x5a0>
   119bc:	0014e713          	ori	a4,s1,1
   119c0:	00e42223          	sw	a4,4(s0)
   119c4:	009404b3          	add	s1,s0,s1
   119c8:	0099a423          	sw	s1,8(s3)
   119cc:	0017e793          	ori	a5,a5,1
   119d0:	00090513          	mv	a0,s2
   119d4:	00f4a223          	sw	a5,4(s1)
   119d8:	69c000ef          	jal	ra,12074 <__malloc_unlock>
   119dc:	00840513          	addi	a0,s0,8
   119e0:	e11ff06f          	j	117f0 <_malloc_r+0x234>
   119e4:	00c42683          	lw	a3,12(s0)
   119e8:	00842603          	lw	a2,8(s0)
   119ec:	c4dff06f          	j	11638 <_malloc_r+0x7c>
   119f0:	0095d793          	srli	a5,a1,0x9
   119f4:	00400713          	li	a4,4
   119f8:	14f77263          	bgeu	a4,a5,11b3c <_malloc_r+0x580>
   119fc:	01400713          	li	a4,20
   11a00:	22f76a63          	bltu	a4,a5,11c34 <_malloc_r+0x678>
   11a04:	05c78693          	addi	a3,a5,92
   11a08:	05b78713          	addi	a4,a5,91
   11a0c:	00369693          	slli	a3,a3,0x3
   11a10:	00d986b3          	add	a3,s3,a3
   11a14:	0006a783          	lw	a5,0(a3)
   11a18:	ff868693          	addi	a3,a3,-8
   11a1c:	1cf68863          	beq	a3,a5,11bec <_malloc_r+0x630>
   11a20:	0047a703          	lw	a4,4(a5)
   11a24:	ffc77713          	andi	a4,a4,-4
   11a28:	00e5f663          	bgeu	a1,a4,11a34 <_malloc_r+0x478>
   11a2c:	0087a783          	lw	a5,8(a5)
   11a30:	fef698e3          	bne	a3,a5,11a20 <_malloc_r+0x464>
   11a34:	00c7a683          	lw	a3,12(a5)
   11a38:	0049a703          	lw	a4,4(s3)
   11a3c:	00d42623          	sw	a3,12(s0)
   11a40:	00f42423          	sw	a5,8(s0)
   11a44:	0086a423          	sw	s0,8(a3)
   11a48:	0087a623          	sw	s0,12(a5)
   11a4c:	cf9ff06f          	j	11744 <_malloc_r+0x188>
   11a50:	01400713          	li	a4,20
   11a54:	12f77663          	bgeu	a4,a5,11b80 <_malloc_r+0x5c4>
   11a58:	05400713          	li	a4,84
   11a5c:	1ef76a63          	bltu	a4,a5,11c50 <_malloc_r+0x694>
   11a60:	00c4d793          	srli	a5,s1,0xc
   11a64:	06f78613          	addi	a2,a5,111
   11a68:	06e78513          	addi	a0,a5,110
   11a6c:	00361693          	slli	a3,a2,0x3
   11a70:	c29ff06f          	j	11698 <_malloc_r+0xdc>
   11a74:	001e0e13          	addi	t3,t3,1
   11a78:	003e7793          	andi	a5,t3,3
   11a7c:	00850513          	addi	a0,a0,8
   11a80:	10078e63          	beqz	a5,11b9c <_malloc_r+0x5e0>
   11a84:	00c52783          	lw	a5,12(a0)
   11a88:	d11ff06f          	j	11798 <_malloc_r+0x1dc>
   11a8c:	00842603          	lw	a2,8(s0)
   11a90:	0014e593          	ori	a1,s1,1
   11a94:	00b42223          	sw	a1,4(s0)
   11a98:	00f62623          	sw	a5,12(a2)
   11a9c:	00c7a423          	sw	a2,8(a5)
   11aa0:	009404b3          	add	s1,s0,s1
   11aa4:	0099aa23          	sw	s1,20(s3)
   11aa8:	0099a823          	sw	s1,16(s3)
   11aac:	0016e793          	ori	a5,a3,1
   11ab0:	0114a623          	sw	a7,12(s1)
   11ab4:	0114a423          	sw	a7,8(s1)
   11ab8:	00f4a223          	sw	a5,4(s1)
   11abc:	00e40733          	add	a4,s0,a4
   11ac0:	00090513          	mv	a0,s2
   11ac4:	00d72023          	sw	a3,0(a4)
   11ac8:	5ac000ef          	jal	ra,12074 <__malloc_unlock>
   11acc:	00840513          	addi	a0,s0,8
   11ad0:	d21ff06f          	j	117f0 <_malloc_r+0x234>
   11ad4:	0034d613          	srli	a2,s1,0x3
   11ad8:	00848793          	addi	a5,s1,8
   11adc:	b39ff06f          	j	11614 <_malloc_r+0x58>
   11ae0:	00b405b3          	add	a1,s0,a1
   11ae4:	0045a783          	lw	a5,4(a1)
   11ae8:	00090513          	mv	a0,s2
   11aec:	0017e793          	ori	a5,a5,1
   11af0:	00f5a223          	sw	a5,4(a1)
   11af4:	580000ef          	jal	ra,12074 <__malloc_unlock>
   11af8:	00840513          	addi	a0,s0,8
   11afc:	cf5ff06f          	j	117f0 <_malloc_r+0x234>
   11b00:	0014e713          	ori	a4,s1,1
   11b04:	00e42223          	sw	a4,4(s0)
   11b08:	009404b3          	add	s1,s0,s1
   11b0c:	0099aa23          	sw	s1,20(s3)
   11b10:	0099a823          	sw	s1,16(s3)
   11b14:	0017e713          	ori	a4,a5,1
   11b18:	0114a623          	sw	a7,12(s1)
   11b1c:	0114a423          	sw	a7,8(s1)
   11b20:	00e4a223          	sw	a4,4(s1)
   11b24:	00b405b3          	add	a1,s0,a1
   11b28:	00090513          	mv	a0,s2
   11b2c:	00f5a023          	sw	a5,0(a1)
   11b30:	544000ef          	jal	ra,12074 <__malloc_unlock>
   11b34:	00840513          	addi	a0,s0,8
   11b38:	cb9ff06f          	j	117f0 <_malloc_r+0x234>
   11b3c:	0065d793          	srli	a5,a1,0x6
   11b40:	03978693          	addi	a3,a5,57
   11b44:	03878713          	addi	a4,a5,56
   11b48:	00369693          	slli	a3,a3,0x3
   11b4c:	ec5ff06f          	j	11a10 <_malloc_r+0x454>
   11b50:	11340e63          	beq	s0,s3,11c6c <_malloc_r+0x6b0>
   11b54:	0089a403          	lw	s0,8(s3)
   11b58:	00442a83          	lw	s5,4(s0)
   11b5c:	ffcafa93          	andi	s5,s5,-4
   11b60:	409a87b3          	sub	a5,s5,s1
   11b64:	009ae663          	bltu	s5,s1,11b70 <_malloc_r+0x5b4>
   11b68:	00f00713          	li	a4,15
   11b6c:	e4f748e3          	blt	a4,a5,119bc <_malloc_r+0x400>
   11b70:	00090513          	mv	a0,s2
   11b74:	500000ef          	jal	ra,12074 <__malloc_unlock>
   11b78:	00000513          	li	a0,0
   11b7c:	c75ff06f          	j	117f0 <_malloc_r+0x234>
   11b80:	05c78613          	addi	a2,a5,92
   11b84:	05b78513          	addi	a0,a5,91
   11b88:	00361693          	slli	a3,a2,0x3
   11b8c:	b0dff06f          	j	11698 <_malloc_r+0xdc>
   11b90:	00832783          	lw	a5,8(t1) # 101ac <frame_dummy+0x1c>
   11b94:	fff60613          	addi	a2,a2,-1
   11b98:	1c679063          	bne	a5,t1,11d58 <_malloc_r+0x79c>
   11b9c:	00367793          	andi	a5,a2,3
   11ba0:	ff830313          	addi	t1,t1,-8
   11ba4:	fe0796e3          	bnez	a5,11b90 <_malloc_r+0x5d4>
   11ba8:	0049a703          	lw	a4,4(s3)
   11bac:	fff5c793          	not	a5,a1
   11bb0:	00e7f7b3          	and	a5,a5,a4
   11bb4:	00f9a223          	sw	a5,4(s3)
   11bb8:	00159593          	slli	a1,a1,0x1
   11bbc:	cab7e2e3          	bltu	a5,a1,11860 <_malloc_r+0x2a4>
   11bc0:	ca0580e3          	beqz	a1,11860 <_malloc_r+0x2a4>
   11bc4:	00f5f733          	and	a4,a1,a5
   11bc8:	00071a63          	bnez	a4,11bdc <_malloc_r+0x620>
   11bcc:	00159593          	slli	a1,a1,0x1
   11bd0:	00f5f733          	and	a4,a1,a5
   11bd4:	004e0e13          	addi	t3,t3,4
   11bd8:	fe070ae3          	beqz	a4,11bcc <_malloc_r+0x610>
   11bdc:	000e0613          	mv	a2,t3
   11be0:	ba5ff06f          	j	11784 <_malloc_r+0x1c8>
   11be4:	010a8a93          	addi	s5,s5,16
   11be8:	cc5ff06f          	j	118ac <_malloc_r+0x2f0>
   11bec:	0049a503          	lw	a0,4(s3)
   11bf0:	40275593          	srai	a1,a4,0x2
   11bf4:	00100713          	li	a4,1
   11bf8:	00b71733          	sll	a4,a4,a1
   11bfc:	00a76733          	or	a4,a4,a0
   11c00:	00e9a223          	sw	a4,4(s3)
   11c04:	e39ff06f          	j	11a3c <_malloc_r+0x480>
   11c08:	015b85b3          	add	a1,s7,s5
   11c0c:	40b005b3          	neg	a1,a1
   11c10:	01459593          	slli	a1,a1,0x14
   11c14:	0145da13          	srli	s4,a1,0x14
   11c18:	000a0593          	mv	a1,s4
   11c1c:	00090513          	mv	a0,s2
   11c20:	1b1000ef          	jal	ra,125d0 <_sbrk_r>
   11c24:	fff00793          	li	a5,-1
   11c28:	d0f518e3          	bne	a0,a5,11938 <_malloc_r+0x37c>
   11c2c:	00000a13          	li	s4,0
   11c30:	d11ff06f          	j	11940 <_malloc_r+0x384>
   11c34:	05400713          	li	a4,84
   11c38:	08f76063          	bltu	a4,a5,11cb8 <_malloc_r+0x6fc>
   11c3c:	00c5d793          	srli	a5,a1,0xc
   11c40:	06f78693          	addi	a3,a5,111
   11c44:	06e78713          	addi	a4,a5,110
   11c48:	00369693          	slli	a3,a3,0x3
   11c4c:	dc5ff06f          	j	11a10 <_malloc_r+0x454>
   11c50:	15400713          	li	a4,340
   11c54:	08f76063          	bltu	a4,a5,11cd4 <_malloc_r+0x718>
   11c58:	00f4d793          	srli	a5,s1,0xf
   11c5c:	07878613          	addi	a2,a5,120
   11c60:	07778513          	addi	a0,a5,119
   11c64:	00361693          	slli	a3,a2,0x3
   11c68:	a31ff06f          	j	11698 <_malloc_r+0xdc>
   11c6c:	07418c13          	addi	s8,gp,116 # 17bdc <__malloc_current_mallinfo>
   11c70:	000c2783          	lw	a5,0(s8)
   11c74:	00fa87b3          	add	a5,s5,a5
   11c78:	00fc2023          	sw	a5,0(s8)
   11c7c:	c65ff06f          	j	118e0 <_malloc_r+0x324>
   11c80:	014a1713          	slli	a4,s4,0x14
   11c84:	c4071ee3          	bnez	a4,118e0 <_malloc_r+0x324>
   11c88:	0089a403          	lw	s0,8(s3)
   11c8c:	015b0ab3          	add	s5,s6,s5
   11c90:	001aea93          	ori	s5,s5,1
   11c94:	01542223          	sw	s5,4(s0)
   11c98:	d01ff06f          	j	11998 <_malloc_r+0x3dc>
   11c9c:	017ca023          	sw	s7,0(s9)
   11ca0:	c59ff06f          	j	118f8 <_malloc_r+0x33c>
   11ca4:	000b8413          	mv	s0,s7
   11ca8:	cf1ff06f          	j	11998 <_malloc_r+0x3dc>
   11cac:	00100793          	li	a5,1
   11cb0:	00fba223          	sw	a5,4(s7)
   11cb4:	ebdff06f          	j	11b70 <_malloc_r+0x5b4>
   11cb8:	15400713          	li	a4,340
   11cbc:	06f76263          	bltu	a4,a5,11d20 <_malloc_r+0x764>
   11cc0:	00f5d793          	srli	a5,a1,0xf
   11cc4:	07878693          	addi	a3,a5,120
   11cc8:	07778713          	addi	a4,a5,119
   11ccc:	00369693          	slli	a3,a3,0x3
   11cd0:	d41ff06f          	j	11a10 <_malloc_r+0x454>
   11cd4:	55400713          	li	a4,1364
   11cd8:	06f76263          	bltu	a4,a5,11d3c <_malloc_r+0x780>
   11cdc:	0124d793          	srli	a5,s1,0x12
   11ce0:	07d78613          	addi	a2,a5,125
   11ce4:	07c78513          	addi	a0,a5,124
   11ce8:	00361693          	slli	a3,a2,0x3
   11cec:	9adff06f          	j	11698 <_malloc_r+0xdc>
   11cf0:	ff8c8c93          	addi	s9,s9,-8
   11cf4:	019a8ab3          	add	s5,s5,s9
   11cf8:	417a8ab3          	sub	s5,s5,s7
   11cfc:	00000a13          	li	s4,0
   11d00:	c41ff06f          	j	11940 <_malloc_r+0x384>
   11d04:	00840593          	addi	a1,s0,8
   11d08:	00090513          	mv	a0,s2
   11d0c:	2a8010ef          	jal	ra,12fb4 <_free_r>
   11d10:	0089a403          	lw	s0,8(s3)
   11d14:	000c2583          	lw	a1,0(s8)
   11d18:	00442a83          	lw	s5,4(s0)
   11d1c:	c7dff06f          	j	11998 <_malloc_r+0x3dc>
   11d20:	55400713          	li	a4,1364
   11d24:	02f76463          	bltu	a4,a5,11d4c <_malloc_r+0x790>
   11d28:	0125d793          	srli	a5,a1,0x12
   11d2c:	07d78693          	addi	a3,a5,125
   11d30:	07c78713          	addi	a4,a5,124
   11d34:	00369693          	slli	a3,a3,0x3
   11d38:	cd9ff06f          	j	11a10 <_malloc_r+0x454>
   11d3c:	3f800693          	li	a3,1016
   11d40:	07f00613          	li	a2,127
   11d44:	07e00513          	li	a0,126
   11d48:	951ff06f          	j	11698 <_malloc_r+0xdc>
   11d4c:	3f800693          	li	a3,1016
   11d50:	07e00713          	li	a4,126
   11d54:	cbdff06f          	j	11a10 <_malloc_r+0x454>
   11d58:	0049a783          	lw	a5,4(s3)
   11d5c:	e5dff06f          	j	11bb8 <_malloc_r+0x5fc>

00011d60 <memchr>:
   11d60:	00357793          	andi	a5,a0,3
   11d64:	0ff5f693          	zext.b	a3,a1
   11d68:	02078a63          	beqz	a5,11d9c <memchr+0x3c>
   11d6c:	fff60793          	addi	a5,a2,-1
   11d70:	02060e63          	beqz	a2,11dac <memchr+0x4c>
   11d74:	fff00613          	li	a2,-1
   11d78:	0180006f          	j	11d90 <memchr+0x30>
   11d7c:	00150513          	addi	a0,a0,1
   11d80:	00357713          	andi	a4,a0,3
   11d84:	00070e63          	beqz	a4,11da0 <memchr+0x40>
   11d88:	fff78793          	addi	a5,a5,-1
   11d8c:	02c78063          	beq	a5,a2,11dac <memchr+0x4c>
   11d90:	00054703          	lbu	a4,0(a0)
   11d94:	fed714e3          	bne	a4,a3,11d7c <memchr+0x1c>
   11d98:	00008067          	ret
   11d9c:	00060793          	mv	a5,a2
   11da0:	00300713          	li	a4,3
   11da4:	02f76663          	bltu	a4,a5,11dd0 <memchr+0x70>
   11da8:	00079663          	bnez	a5,11db4 <memchr+0x54>
   11dac:	00000513          	li	a0,0
   11db0:	00008067          	ret
   11db4:	00f507b3          	add	a5,a0,a5
   11db8:	00c0006f          	j	11dc4 <memchr+0x64>
   11dbc:	00150513          	addi	a0,a0,1
   11dc0:	fea786e3          	beq	a5,a0,11dac <memchr+0x4c>
   11dc4:	00054703          	lbu	a4,0(a0)
   11dc8:	fed71ae3          	bne	a4,a3,11dbc <memchr+0x5c>
   11dcc:	00008067          	ret
   11dd0:	0ff5f593          	zext.b	a1,a1
   11dd4:	00859713          	slli	a4,a1,0x8
   11dd8:	00b76733          	or	a4,a4,a1
   11ddc:	01071893          	slli	a7,a4,0x10
   11de0:	feff0837          	lui	a6,0xfeff0
   11de4:	808085b7          	lui	a1,0x80808
   11de8:	00e8e8b3          	or	a7,a7,a4
   11dec:	eff80813          	addi	a6,a6,-257 # fefefeff <__BSS_END__+0xfefd82fb>
   11df0:	08058593          	addi	a1,a1,128 # 80808080 <__BSS_END__+0x807f047c>
   11df4:	00300313          	li	t1,3
   11df8:	00052703          	lw	a4,0(a0)
   11dfc:	00e8c733          	xor	a4,a7,a4
   11e00:	01070633          	add	a2,a4,a6
   11e04:	fff74713          	not	a4,a4
   11e08:	00e67733          	and	a4,a2,a4
   11e0c:	00b77733          	and	a4,a4,a1
   11e10:	fa0712e3          	bnez	a4,11db4 <memchr+0x54>
   11e14:	ffc78793          	addi	a5,a5,-4
   11e18:	00450513          	addi	a0,a0,4
   11e1c:	fcf36ee3          	bltu	t1,a5,11df8 <memchr+0x98>
   11e20:	f8079ae3          	bnez	a5,11db4 <memchr+0x54>
   11e24:	f89ff06f          	j	11dac <memchr+0x4c>

00011e28 <memcpy>:
   11e28:	00b547b3          	xor	a5,a0,a1
   11e2c:	0037f793          	andi	a5,a5,3
   11e30:	00c508b3          	add	a7,a0,a2
   11e34:	06079663          	bnez	a5,11ea0 <memcpy+0x78>
   11e38:	00300793          	li	a5,3
   11e3c:	06c7f263          	bgeu	a5,a2,11ea0 <memcpy+0x78>
   11e40:	00357793          	andi	a5,a0,3
   11e44:	00050713          	mv	a4,a0
   11e48:	0c079a63          	bnez	a5,11f1c <memcpy+0xf4>
   11e4c:	ffc8f613          	andi	a2,a7,-4
   11e50:	40e606b3          	sub	a3,a2,a4
   11e54:	02000793          	li	a5,32
   11e58:	02000293          	li	t0,32
   11e5c:	06d7c263          	blt	a5,a3,11ec0 <memcpy+0x98>
   11e60:	00058693          	mv	a3,a1
   11e64:	00070793          	mv	a5,a4
   11e68:	02c77863          	bgeu	a4,a2,11e98 <memcpy+0x70>
   11e6c:	0006a803          	lw	a6,0(a3)
   11e70:	00478793          	addi	a5,a5,4
   11e74:	00468693          	addi	a3,a3,4
   11e78:	ff07ae23          	sw	a6,-4(a5)
   11e7c:	fec7e8e3          	bltu	a5,a2,11e6c <memcpy+0x44>
   11e80:	fff60793          	addi	a5,a2,-1
   11e84:	40e787b3          	sub	a5,a5,a4
   11e88:	ffc7f793          	andi	a5,a5,-4
   11e8c:	00478793          	addi	a5,a5,4
   11e90:	00f70733          	add	a4,a4,a5
   11e94:	00f585b3          	add	a1,a1,a5
   11e98:	01176863          	bltu	a4,a7,11ea8 <memcpy+0x80>
   11e9c:	00008067          	ret
   11ea0:	00050713          	mv	a4,a0
   11ea4:	ff157ce3          	bgeu	a0,a7,11e9c <memcpy+0x74>
   11ea8:	0005c783          	lbu	a5,0(a1)
   11eac:	00170713          	addi	a4,a4,1
   11eb0:	00158593          	addi	a1,a1,1
   11eb4:	fef70fa3          	sb	a5,-1(a4)
   11eb8:	ff1768e3          	bltu	a4,a7,11ea8 <memcpy+0x80>
   11ebc:	00008067          	ret
   11ec0:	0045a683          	lw	a3,4(a1)
   11ec4:	01c5a783          	lw	a5,28(a1)
   11ec8:	0005af83          	lw	t6,0(a1)
   11ecc:	0085af03          	lw	t5,8(a1)
   11ed0:	00c5ae83          	lw	t4,12(a1)
   11ed4:	0105ae03          	lw	t3,16(a1)
   11ed8:	0145a303          	lw	t1,20(a1)
   11edc:	0185a803          	lw	a6,24(a1)
   11ee0:	00d72223          	sw	a3,4(a4)
   11ee4:	0205a683          	lw	a3,32(a1)
   11ee8:	01f72023          	sw	t6,0(a4)
   11eec:	01e72423          	sw	t5,8(a4)
   11ef0:	01d72623          	sw	t4,12(a4)
   11ef4:	01c72823          	sw	t3,16(a4)
   11ef8:	00672a23          	sw	t1,20(a4)
   11efc:	01072c23          	sw	a6,24(a4)
   11f00:	00f72e23          	sw	a5,28(a4)
   11f04:	02470713          	addi	a4,a4,36
   11f08:	40e607b3          	sub	a5,a2,a4
   11f0c:	fed72e23          	sw	a3,-4(a4)
   11f10:	02458593          	addi	a1,a1,36
   11f14:	faf2c6e3          	blt	t0,a5,11ec0 <memcpy+0x98>
   11f18:	f49ff06f          	j	11e60 <memcpy+0x38>
   11f1c:	0005c683          	lbu	a3,0(a1)
   11f20:	00170713          	addi	a4,a4,1
   11f24:	00377793          	andi	a5,a4,3
   11f28:	fed70fa3          	sb	a3,-1(a4)
   11f2c:	00158593          	addi	a1,a1,1
   11f30:	f0078ee3          	beqz	a5,11e4c <memcpy+0x24>
   11f34:	0005c683          	lbu	a3,0(a1)
   11f38:	00170713          	addi	a4,a4,1
   11f3c:	00377793          	andi	a5,a4,3
   11f40:	fed70fa3          	sb	a3,-1(a4)
   11f44:	00158593          	addi	a1,a1,1
   11f48:	fc079ae3          	bnez	a5,11f1c <memcpy+0xf4>
   11f4c:	f01ff06f          	j	11e4c <memcpy+0x24>

00011f50 <memmove>:
   11f50:	02a5f663          	bgeu	a1,a0,11f7c <memmove+0x2c>
   11f54:	00c587b3          	add	a5,a1,a2
   11f58:	02f57263          	bgeu	a0,a5,11f7c <memmove+0x2c>
   11f5c:	00c50733          	add	a4,a0,a2
   11f60:	0e060a63          	beqz	a2,12054 <memmove+0x104>
   11f64:	fff7c683          	lbu	a3,-1(a5)
   11f68:	fff78793          	addi	a5,a5,-1
   11f6c:	fff70713          	addi	a4,a4,-1
   11f70:	00d70023          	sb	a3,0(a4)
   11f74:	fef598e3          	bne	a1,a5,11f64 <memmove+0x14>
   11f78:	00008067          	ret
   11f7c:	00f00793          	li	a5,15
   11f80:	02c7e863          	bltu	a5,a2,11fb0 <memmove+0x60>
   11f84:	00050793          	mv	a5,a0
   11f88:	fff60693          	addi	a3,a2,-1
   11f8c:	0c060c63          	beqz	a2,12064 <memmove+0x114>
   11f90:	00168693          	addi	a3,a3,1
   11f94:	00d786b3          	add	a3,a5,a3
   11f98:	0005c703          	lbu	a4,0(a1)
   11f9c:	00178793          	addi	a5,a5,1
   11fa0:	00158593          	addi	a1,a1,1
   11fa4:	fee78fa3          	sb	a4,-1(a5)
   11fa8:	fed798e3          	bne	a5,a3,11f98 <memmove+0x48>
   11fac:	00008067          	ret
   11fb0:	00b567b3          	or	a5,a0,a1
   11fb4:	0037f793          	andi	a5,a5,3
   11fb8:	0a079063          	bnez	a5,12058 <memmove+0x108>
   11fbc:	ff060893          	addi	a7,a2,-16
   11fc0:	ff08f893          	andi	a7,a7,-16
   11fc4:	01088893          	addi	a7,a7,16
   11fc8:	01150833          	add	a6,a0,a7
   11fcc:	00058713          	mv	a4,a1
   11fd0:	00050793          	mv	a5,a0
   11fd4:	00072683          	lw	a3,0(a4)
   11fd8:	01070713          	addi	a4,a4,16
   11fdc:	01078793          	addi	a5,a5,16
   11fe0:	fed7a823          	sw	a3,-16(a5)
   11fe4:	ff472683          	lw	a3,-12(a4)
   11fe8:	fed7aa23          	sw	a3,-12(a5)
   11fec:	ff872683          	lw	a3,-8(a4)
   11ff0:	fed7ac23          	sw	a3,-8(a5)
   11ff4:	ffc72683          	lw	a3,-4(a4)
   11ff8:	fed7ae23          	sw	a3,-4(a5)
   11ffc:	fcf81ce3          	bne	a6,a5,11fd4 <memmove+0x84>
   12000:	00c67713          	andi	a4,a2,12
   12004:	011585b3          	add	a1,a1,a7
   12008:	00f67813          	andi	a6,a2,15
   1200c:	04070e63          	beqz	a4,12068 <memmove+0x118>
   12010:	00058713          	mv	a4,a1
   12014:	00078893          	mv	a7,a5
   12018:	00300e13          	li	t3,3
   1201c:	00072303          	lw	t1,0(a4)
   12020:	00470713          	addi	a4,a4,4
   12024:	40e806b3          	sub	a3,a6,a4
   12028:	0068a023          	sw	t1,0(a7)
   1202c:	00d586b3          	add	a3,a1,a3
   12030:	00488893          	addi	a7,a7,4
   12034:	fede64e3          	bltu	t3,a3,1201c <memmove+0xcc>
   12038:	ffc80713          	addi	a4,a6,-4
   1203c:	ffc77713          	andi	a4,a4,-4
   12040:	00470713          	addi	a4,a4,4
   12044:	00367613          	andi	a2,a2,3
   12048:	00e787b3          	add	a5,a5,a4
   1204c:	00e585b3          	add	a1,a1,a4
   12050:	f39ff06f          	j	11f88 <memmove+0x38>
   12054:	00008067          	ret
   12058:	fff60693          	addi	a3,a2,-1
   1205c:	00050793          	mv	a5,a0
   12060:	f31ff06f          	j	11f90 <memmove+0x40>
   12064:	00008067          	ret
   12068:	00080613          	mv	a2,a6
   1206c:	f1dff06f          	j	11f88 <memmove+0x38>

00012070 <__malloc_lock>:
   12070:	00008067          	ret

00012074 <__malloc_unlock>:
   12074:	00008067          	ret

00012078 <_realloc_r>:
   12078:	fd010113          	addi	sp,sp,-48
   1207c:	03212023          	sw	s2,32(sp)
   12080:	02112623          	sw	ra,44(sp)
   12084:	02812423          	sw	s0,40(sp)
   12088:	02912223          	sw	s1,36(sp)
   1208c:	01312e23          	sw	s3,28(sp)
   12090:	01412c23          	sw	s4,24(sp)
   12094:	01512a23          	sw	s5,20(sp)
   12098:	01612823          	sw	s6,16(sp)
   1209c:	01712623          	sw	s7,12(sp)
   120a0:	01812423          	sw	s8,8(sp)
   120a4:	00060913          	mv	s2,a2
   120a8:	1c058463          	beqz	a1,12270 <_realloc_r+0x1f8>
   120ac:	00058413          	mv	s0,a1
   120b0:	00050993          	mv	s3,a0
   120b4:	fbdff0ef          	jal	ra,12070 <__malloc_lock>
   120b8:	00b90493          	addi	s1,s2,11
   120bc:	01600713          	li	a4,22
   120c0:	ffc42783          	lw	a5,-4(s0)
   120c4:	0e977a63          	bgeu	a4,s1,121b8 <_realloc_r+0x140>
   120c8:	ff84f493          	andi	s1,s1,-8
   120cc:	00048713          	mv	a4,s1
   120d0:	0e04ca63          	bltz	s1,121c4 <_realloc_r+0x14c>
   120d4:	0f24e863          	bltu	s1,s2,121c4 <_realloc_r+0x14c>
   120d8:	ffc7fa13          	andi	s4,a5,-4
   120dc:	ff840a93          	addi	s5,s0,-8
   120e0:	12ea5c63          	bge	s4,a4,12218 <_realloc_r+0x1a0>
   120e4:	c2818c13          	addi	s8,gp,-984 # 17790 <__malloc_av_>
   120e8:	008c2583          	lw	a1,8(s8)
   120ec:	014a8633          	add	a2,s5,s4
   120f0:	00462683          	lw	a3,4(a2)
   120f4:	1ec58063          	beq	a1,a2,122d4 <_realloc_r+0x25c>
   120f8:	ffe6f593          	andi	a1,a3,-2
   120fc:	00b605b3          	add	a1,a2,a1
   12100:	0045a583          	lw	a1,4(a1)
   12104:	0015f593          	andi	a1,a1,1
   12108:	14059663          	bnez	a1,12254 <_realloc_r+0x1dc>
   1210c:	ffc6f693          	andi	a3,a3,-4
   12110:	00da05b3          	add	a1,s4,a3
   12114:	0ee5d863          	bge	a1,a4,12204 <_realloc_r+0x18c>
   12118:	0017f793          	andi	a5,a5,1
   1211c:	02079463          	bnez	a5,12144 <_realloc_r+0xcc>
   12120:	ff842b83          	lw	s7,-8(s0)
   12124:	417a8bb3          	sub	s7,s5,s7
   12128:	004ba783          	lw	a5,4(s7)
   1212c:	ffc7f793          	andi	a5,a5,-4
   12130:	00d786b3          	add	a3,a5,a3
   12134:	01468b33          	add	s6,a3,s4
   12138:	36eb5063          	bge	s6,a4,12498 <_realloc_r+0x420>
   1213c:	00fa0b33          	add	s6,s4,a5
   12140:	2ceb5263          	bge	s6,a4,12404 <_realloc_r+0x38c>
   12144:	00090593          	mv	a1,s2
   12148:	00098513          	mv	a0,s3
   1214c:	c70ff0ef          	jal	ra,115bc <_malloc_r>
   12150:	00050913          	mv	s2,a0
   12154:	04050c63          	beqz	a0,121ac <_realloc_r+0x134>
   12158:	ffc42783          	lw	a5,-4(s0)
   1215c:	ff850713          	addi	a4,a0,-8
   12160:	ffe7f793          	andi	a5,a5,-2
   12164:	00fa87b3          	add	a5,s5,a5
   12168:	28e78663          	beq	a5,a4,123f4 <_realloc_r+0x37c>
   1216c:	ffca0613          	addi	a2,s4,-4
   12170:	02400793          	li	a5,36
   12174:	30c7ec63          	bltu	a5,a2,1248c <_realloc_r+0x414>
   12178:	01300713          	li	a4,19
   1217c:	22c76063          	bltu	a4,a2,1239c <_realloc_r+0x324>
   12180:	00050793          	mv	a5,a0
   12184:	00040713          	mv	a4,s0
   12188:	00072683          	lw	a3,0(a4)
   1218c:	00d7a023          	sw	a3,0(a5)
   12190:	00472683          	lw	a3,4(a4)
   12194:	00d7a223          	sw	a3,4(a5)
   12198:	00872703          	lw	a4,8(a4)
   1219c:	00e7a423          	sw	a4,8(a5)
   121a0:	00040593          	mv	a1,s0
   121a4:	00098513          	mv	a0,s3
   121a8:	60d000ef          	jal	ra,12fb4 <_free_r>
   121ac:	00098513          	mv	a0,s3
   121b0:	ec5ff0ef          	jal	ra,12074 <__malloc_unlock>
   121b4:	01c0006f          	j	121d0 <_realloc_r+0x158>
   121b8:	01000493          	li	s1,16
   121bc:	01000713          	li	a4,16
   121c0:	f124fce3          	bgeu	s1,s2,120d8 <_realloc_r+0x60>
   121c4:	00c00793          	li	a5,12
   121c8:	00f9a023          	sw	a5,0(s3)
   121cc:	00000913          	li	s2,0
   121d0:	02c12083          	lw	ra,44(sp)
   121d4:	02812403          	lw	s0,40(sp)
   121d8:	02412483          	lw	s1,36(sp)
   121dc:	01c12983          	lw	s3,28(sp)
   121e0:	01812a03          	lw	s4,24(sp)
   121e4:	01412a83          	lw	s5,20(sp)
   121e8:	01012b03          	lw	s6,16(sp)
   121ec:	00c12b83          	lw	s7,12(sp)
   121f0:	00812c03          	lw	s8,8(sp)
   121f4:	00090513          	mv	a0,s2
   121f8:	02012903          	lw	s2,32(sp)
   121fc:	03010113          	addi	sp,sp,48
   12200:	00008067          	ret
   12204:	00c62783          	lw	a5,12(a2)
   12208:	00862703          	lw	a4,8(a2)
   1220c:	00058a13          	mv	s4,a1
   12210:	00f72623          	sw	a5,12(a4)
   12214:	00e7a423          	sw	a4,8(a5)
   12218:	004aa783          	lw	a5,4(s5)
   1221c:	409a06b3          	sub	a3,s4,s1
   12220:	00f00613          	li	a2,15
   12224:	0017f793          	andi	a5,a5,1
   12228:	014a8733          	add	a4,s5,s4
   1222c:	06d66c63          	bltu	a2,a3,122a4 <_realloc_r+0x22c>
   12230:	00fa67b3          	or	a5,s4,a5
   12234:	00faa223          	sw	a5,4(s5)
   12238:	00472783          	lw	a5,4(a4)
   1223c:	0017e793          	ori	a5,a5,1
   12240:	00f72223          	sw	a5,4(a4)
   12244:	00098513          	mv	a0,s3
   12248:	e2dff0ef          	jal	ra,12074 <__malloc_unlock>
   1224c:	00040913          	mv	s2,s0
   12250:	f81ff06f          	j	121d0 <_realloc_r+0x158>
   12254:	0017f793          	andi	a5,a5,1
   12258:	ee0796e3          	bnez	a5,12144 <_realloc_r+0xcc>
   1225c:	ff842b83          	lw	s7,-8(s0)
   12260:	417a8bb3          	sub	s7,s5,s7
   12264:	004ba783          	lw	a5,4(s7)
   12268:	ffc7f793          	andi	a5,a5,-4
   1226c:	ed1ff06f          	j	1213c <_realloc_r+0xc4>
   12270:	02812403          	lw	s0,40(sp)
   12274:	02c12083          	lw	ra,44(sp)
   12278:	02412483          	lw	s1,36(sp)
   1227c:	02012903          	lw	s2,32(sp)
   12280:	01c12983          	lw	s3,28(sp)
   12284:	01812a03          	lw	s4,24(sp)
   12288:	01412a83          	lw	s5,20(sp)
   1228c:	01012b03          	lw	s6,16(sp)
   12290:	00c12b83          	lw	s7,12(sp)
   12294:	00812c03          	lw	s8,8(sp)
   12298:	00060593          	mv	a1,a2
   1229c:	03010113          	addi	sp,sp,48
   122a0:	b1cff06f          	j	115bc <_malloc_r>
   122a4:	0097e7b3          	or	a5,a5,s1
   122a8:	00faa223          	sw	a5,4(s5)
   122ac:	009a85b3          	add	a1,s5,s1
   122b0:	0016e693          	ori	a3,a3,1
   122b4:	00d5a223          	sw	a3,4(a1)
   122b8:	00472783          	lw	a5,4(a4)
   122bc:	00858593          	addi	a1,a1,8
   122c0:	00098513          	mv	a0,s3
   122c4:	0017e793          	ori	a5,a5,1
   122c8:	00f72223          	sw	a5,4(a4)
   122cc:	4e9000ef          	jal	ra,12fb4 <_free_r>
   122d0:	f75ff06f          	j	12244 <_realloc_r+0x1cc>
   122d4:	ffc6f693          	andi	a3,a3,-4
   122d8:	00da0633          	add	a2,s4,a3
   122dc:	01048593          	addi	a1,s1,16
   122e0:	0eb65063          	bge	a2,a1,123c0 <_realloc_r+0x348>
   122e4:	0017f793          	andi	a5,a5,1
   122e8:	e4079ee3          	bnez	a5,12144 <_realloc_r+0xcc>
   122ec:	ff842b83          	lw	s7,-8(s0)
   122f0:	417a8bb3          	sub	s7,s5,s7
   122f4:	004ba783          	lw	a5,4(s7)
   122f8:	ffc7f793          	andi	a5,a5,-4
   122fc:	00d786b3          	add	a3,a5,a3
   12300:	01468b33          	add	s6,a3,s4
   12304:	e2bb4ce3          	blt	s6,a1,1213c <_realloc_r+0xc4>
   12308:	00cba783          	lw	a5,12(s7)
   1230c:	008ba703          	lw	a4,8(s7)
   12310:	ffca0613          	addi	a2,s4,-4
   12314:	02400693          	li	a3,36
   12318:	00f72623          	sw	a5,12(a4)
   1231c:	00e7a423          	sw	a4,8(a5)
   12320:	008b8913          	addi	s2,s7,8
   12324:	26c6e063          	bltu	a3,a2,12584 <_realloc_r+0x50c>
   12328:	01300713          	li	a4,19
   1232c:	00090793          	mv	a5,s2
   12330:	02c77263          	bgeu	a4,a2,12354 <_realloc_r+0x2dc>
   12334:	00042703          	lw	a4,0(s0)
   12338:	01b00793          	li	a5,27
   1233c:	00eba423          	sw	a4,8(s7)
   12340:	00442703          	lw	a4,4(s0)
   12344:	00eba623          	sw	a4,12(s7)
   12348:	24c7e663          	bltu	a5,a2,12594 <_realloc_r+0x51c>
   1234c:	00840413          	addi	s0,s0,8
   12350:	010b8793          	addi	a5,s7,16
   12354:	00042703          	lw	a4,0(s0)
   12358:	00e7a023          	sw	a4,0(a5)
   1235c:	00442703          	lw	a4,4(s0)
   12360:	00e7a223          	sw	a4,4(a5)
   12364:	00842703          	lw	a4,8(s0)
   12368:	00e7a423          	sw	a4,8(a5)
   1236c:	009b8733          	add	a4,s7,s1
   12370:	409b07b3          	sub	a5,s6,s1
   12374:	00ec2423          	sw	a4,8(s8)
   12378:	0017e793          	ori	a5,a5,1
   1237c:	00f72223          	sw	a5,4(a4)
   12380:	004ba783          	lw	a5,4(s7)
   12384:	00098513          	mv	a0,s3
   12388:	0017f793          	andi	a5,a5,1
   1238c:	0097e7b3          	or	a5,a5,s1
   12390:	00fba223          	sw	a5,4(s7)
   12394:	ce1ff0ef          	jal	ra,12074 <__malloc_unlock>
   12398:	e39ff06f          	j	121d0 <_realloc_r+0x158>
   1239c:	00042683          	lw	a3,0(s0)
   123a0:	01b00713          	li	a4,27
   123a4:	00d52023          	sw	a3,0(a0)
   123a8:	00442683          	lw	a3,4(s0)
   123ac:	00d52223          	sw	a3,4(a0)
   123b0:	18c76663          	bltu	a4,a2,1253c <_realloc_r+0x4c4>
   123b4:	00840713          	addi	a4,s0,8
   123b8:	00850793          	addi	a5,a0,8
   123bc:	dcdff06f          	j	12188 <_realloc_r+0x110>
   123c0:	009a8ab3          	add	s5,s5,s1
   123c4:	409607b3          	sub	a5,a2,s1
   123c8:	015c2423          	sw	s5,8(s8)
   123cc:	0017e793          	ori	a5,a5,1
   123d0:	00faa223          	sw	a5,4(s5)
   123d4:	ffc42783          	lw	a5,-4(s0)
   123d8:	00098513          	mv	a0,s3
   123dc:	00040913          	mv	s2,s0
   123e0:	0017f793          	andi	a5,a5,1
   123e4:	0097e7b3          	or	a5,a5,s1
   123e8:	fef42e23          	sw	a5,-4(s0)
   123ec:	c89ff0ef          	jal	ra,12074 <__malloc_unlock>
   123f0:	de1ff06f          	j	121d0 <_realloc_r+0x158>
   123f4:	ffc52783          	lw	a5,-4(a0)
   123f8:	ffc7f793          	andi	a5,a5,-4
   123fc:	00fa0a33          	add	s4,s4,a5
   12400:	e19ff06f          	j	12218 <_realloc_r+0x1a0>
   12404:	00cba783          	lw	a5,12(s7)
   12408:	008ba703          	lw	a4,8(s7)
   1240c:	ffca0613          	addi	a2,s4,-4
   12410:	02400693          	li	a3,36
   12414:	00f72623          	sw	a5,12(a4)
   12418:	00e7a423          	sw	a4,8(a5)
   1241c:	008b8913          	addi	s2,s7,8
   12420:	10c6e063          	bltu	a3,a2,12520 <_realloc_r+0x4a8>
   12424:	01300713          	li	a4,19
   12428:	00090793          	mv	a5,s2
   1242c:	02c77c63          	bgeu	a4,a2,12464 <_realloc_r+0x3ec>
   12430:	00042703          	lw	a4,0(s0)
   12434:	01b00793          	li	a5,27
   12438:	00eba423          	sw	a4,8(s7)
   1243c:	00442703          	lw	a4,4(s0)
   12440:	00eba623          	sw	a4,12(s7)
   12444:	10c7fc63          	bgeu	a5,a2,1255c <_realloc_r+0x4e4>
   12448:	00842783          	lw	a5,8(s0)
   1244c:	00fba823          	sw	a5,16(s7)
   12450:	00c42783          	lw	a5,12(s0)
   12454:	00fbaa23          	sw	a5,20(s7)
   12458:	0ad60663          	beq	a2,a3,12504 <_realloc_r+0x48c>
   1245c:	01040413          	addi	s0,s0,16
   12460:	018b8793          	addi	a5,s7,24
   12464:	00042703          	lw	a4,0(s0)
   12468:	000b0a13          	mv	s4,s6
   1246c:	000b8a93          	mv	s5,s7
   12470:	00e7a023          	sw	a4,0(a5)
   12474:	00442703          	lw	a4,4(s0)
   12478:	00e7a223          	sw	a4,4(a5)
   1247c:	00842703          	lw	a4,8(s0)
   12480:	00090413          	mv	s0,s2
   12484:	00e7a423          	sw	a4,8(a5)
   12488:	d91ff06f          	j	12218 <_realloc_r+0x1a0>
   1248c:	00040593          	mv	a1,s0
   12490:	ac1ff0ef          	jal	ra,11f50 <memmove>
   12494:	d0dff06f          	j	121a0 <_realloc_r+0x128>
   12498:	00c62783          	lw	a5,12(a2)
   1249c:	00862703          	lw	a4,8(a2)
   124a0:	02400693          	li	a3,36
   124a4:	ffca0613          	addi	a2,s4,-4
   124a8:	00f72623          	sw	a5,12(a4)
   124ac:	00e7a423          	sw	a4,8(a5)
   124b0:	008ba703          	lw	a4,8(s7)
   124b4:	00cba783          	lw	a5,12(s7)
   124b8:	008b8913          	addi	s2,s7,8
   124bc:	00f72623          	sw	a5,12(a4)
   124c0:	00e7a423          	sw	a4,8(a5)
   124c4:	04c6ee63          	bltu	a3,a2,12520 <_realloc_r+0x4a8>
   124c8:	01300713          	li	a4,19
   124cc:	00090793          	mv	a5,s2
   124d0:	f8c77ae3          	bgeu	a4,a2,12464 <_realloc_r+0x3ec>
   124d4:	00042703          	lw	a4,0(s0)
   124d8:	01b00793          	li	a5,27
   124dc:	00eba423          	sw	a4,8(s7)
   124e0:	00442703          	lw	a4,4(s0)
   124e4:	00eba623          	sw	a4,12(s7)
   124e8:	06c7fa63          	bgeu	a5,a2,1255c <_realloc_r+0x4e4>
   124ec:	00842703          	lw	a4,8(s0)
   124f0:	02400793          	li	a5,36
   124f4:	00eba823          	sw	a4,16(s7)
   124f8:	00c42703          	lw	a4,12(s0)
   124fc:	00ebaa23          	sw	a4,20(s7)
   12500:	f4f61ee3          	bne	a2,a5,1245c <_realloc_r+0x3e4>
   12504:	01042703          	lw	a4,16(s0)
   12508:	020b8793          	addi	a5,s7,32
   1250c:	01840413          	addi	s0,s0,24
   12510:	00ebac23          	sw	a4,24(s7)
   12514:	ffc42703          	lw	a4,-4(s0)
   12518:	00ebae23          	sw	a4,28(s7)
   1251c:	f49ff06f          	j	12464 <_realloc_r+0x3ec>
   12520:	00040593          	mv	a1,s0
   12524:	00090513          	mv	a0,s2
   12528:	a29ff0ef          	jal	ra,11f50 <memmove>
   1252c:	00090413          	mv	s0,s2
   12530:	000b0a13          	mv	s4,s6
   12534:	000b8a93          	mv	s5,s7
   12538:	ce1ff06f          	j	12218 <_realloc_r+0x1a0>
   1253c:	00842703          	lw	a4,8(s0)
   12540:	00e52423          	sw	a4,8(a0)
   12544:	00c42703          	lw	a4,12(s0)
   12548:	00e52623          	sw	a4,12(a0)
   1254c:	00f60e63          	beq	a2,a5,12568 <_realloc_r+0x4f0>
   12550:	01040713          	addi	a4,s0,16
   12554:	01050793          	addi	a5,a0,16
   12558:	c31ff06f          	j	12188 <_realloc_r+0x110>
   1255c:	00840413          	addi	s0,s0,8
   12560:	010b8793          	addi	a5,s7,16
   12564:	f01ff06f          	j	12464 <_realloc_r+0x3ec>
   12568:	01042683          	lw	a3,16(s0)
   1256c:	01840713          	addi	a4,s0,24
   12570:	01850793          	addi	a5,a0,24
   12574:	00d52823          	sw	a3,16(a0)
   12578:	01442683          	lw	a3,20(s0)
   1257c:	00d52a23          	sw	a3,20(a0)
   12580:	c09ff06f          	j	12188 <_realloc_r+0x110>
   12584:	00040593          	mv	a1,s0
   12588:	00090513          	mv	a0,s2
   1258c:	9c5ff0ef          	jal	ra,11f50 <memmove>
   12590:	dddff06f          	j	1236c <_realloc_r+0x2f4>
   12594:	00842783          	lw	a5,8(s0)
   12598:	00fba823          	sw	a5,16(s7)
   1259c:	00c42783          	lw	a5,12(s0)
   125a0:	00fbaa23          	sw	a5,20(s7)
   125a4:	00d60863          	beq	a2,a3,125b4 <_realloc_r+0x53c>
   125a8:	01040413          	addi	s0,s0,16
   125ac:	018b8793          	addi	a5,s7,24
   125b0:	da5ff06f          	j	12354 <_realloc_r+0x2dc>
   125b4:	01042703          	lw	a4,16(s0)
   125b8:	020b8793          	addi	a5,s7,32
   125bc:	01840413          	addi	s0,s0,24
   125c0:	00ebac23          	sw	a4,24(s7)
   125c4:	ffc42703          	lw	a4,-4(s0)
   125c8:	00ebae23          	sw	a4,28(s7)
   125cc:	d89ff06f          	j	12354 <_realloc_r+0x2dc>

000125d0 <_sbrk_r>:
   125d0:	ff010113          	addi	sp,sp,-16
   125d4:	00812423          	sw	s0,8(sp)
   125d8:	00050413          	mv	s0,a0
   125dc:	00058513          	mv	a0,a1
   125e0:	0401a823          	sw	zero,80(gp) # 17bb8 <errno>
   125e4:	00112623          	sw	ra,12(sp)
   125e8:	3e4010ef          	jal	ra,139cc <_sbrk>
   125ec:	fff00793          	li	a5,-1
   125f0:	00f50a63          	beq	a0,a5,12604 <_sbrk_r+0x34>
   125f4:	00c12083          	lw	ra,12(sp)
   125f8:	00812403          	lw	s0,8(sp)
   125fc:	01010113          	addi	sp,sp,16
   12600:	00008067          	ret
   12604:	0501a783          	lw	a5,80(gp) # 17bb8 <errno>
   12608:	fe0786e3          	beqz	a5,125f4 <_sbrk_r+0x24>
   1260c:	00c12083          	lw	ra,12(sp)
   12610:	00f42023          	sw	a5,0(s0)
   12614:	00812403          	lw	s0,8(sp)
   12618:	01010113          	addi	sp,sp,16
   1261c:	00008067          	ret

00012620 <__sread>:
   12620:	ff010113          	addi	sp,sp,-16
   12624:	00812423          	sw	s0,8(sp)
   12628:	00058413          	mv	s0,a1
   1262c:	00e59583          	lh	a1,14(a1)
   12630:	00112623          	sw	ra,12(sp)
   12634:	749000ef          	jal	ra,1357c <_read_r>
   12638:	02054063          	bltz	a0,12658 <__sread+0x38>
   1263c:	05042783          	lw	a5,80(s0)
   12640:	00c12083          	lw	ra,12(sp)
   12644:	00a787b3          	add	a5,a5,a0
   12648:	04f42823          	sw	a5,80(s0)
   1264c:	00812403          	lw	s0,8(sp)
   12650:	01010113          	addi	sp,sp,16
   12654:	00008067          	ret
   12658:	00c45783          	lhu	a5,12(s0)
   1265c:	fffff737          	lui	a4,0xfffff
   12660:	fff70713          	addi	a4,a4,-1 # ffffefff <__BSS_END__+0xfffe73fb>
   12664:	00e7f7b3          	and	a5,a5,a4
   12668:	00c12083          	lw	ra,12(sp)
   1266c:	00f41623          	sh	a5,12(s0)
   12670:	00812403          	lw	s0,8(sp)
   12674:	01010113          	addi	sp,sp,16
   12678:	00008067          	ret

0001267c <__seofread>:
   1267c:	00000513          	li	a0,0
   12680:	00008067          	ret

00012684 <__swrite>:
   12684:	00c59783          	lh	a5,12(a1)
   12688:	fe010113          	addi	sp,sp,-32
   1268c:	00812c23          	sw	s0,24(sp)
   12690:	00912a23          	sw	s1,20(sp)
   12694:	01212823          	sw	s2,16(sp)
   12698:	01312623          	sw	s3,12(sp)
   1269c:	00112e23          	sw	ra,28(sp)
   126a0:	1007f713          	andi	a4,a5,256
   126a4:	00058413          	mv	s0,a1
   126a8:	00050493          	mv	s1,a0
   126ac:	00060913          	mv	s2,a2
   126b0:	00068993          	mv	s3,a3
   126b4:	04071063          	bnez	a4,126f4 <__swrite+0x70>
   126b8:	fffff737          	lui	a4,0xfffff
   126bc:	fff70713          	addi	a4,a4,-1 # ffffefff <__BSS_END__+0xfffe73fb>
   126c0:	00e7f7b3          	and	a5,a5,a4
   126c4:	00e41583          	lh	a1,14(s0)
   126c8:	00f41623          	sh	a5,12(s0)
   126cc:	01812403          	lw	s0,24(sp)
   126d0:	01c12083          	lw	ra,28(sp)
   126d4:	00098693          	mv	a3,s3
   126d8:	00090613          	mv	a2,s2
   126dc:	00c12983          	lw	s3,12(sp)
   126e0:	01012903          	lw	s2,16(sp)
   126e4:	00048513          	mv	a0,s1
   126e8:	01412483          	lw	s1,20(sp)
   126ec:	02010113          	addi	sp,sp,32
   126f0:	08c0006f          	j	1277c <_write_r>
   126f4:	00e59583          	lh	a1,14(a1)
   126f8:	00200693          	li	a3,2
   126fc:	00000613          	li	a2,0
   12700:	3b5000ef          	jal	ra,132b4 <_lseek_r>
   12704:	00c41783          	lh	a5,12(s0)
   12708:	fb1ff06f          	j	126b8 <__swrite+0x34>

0001270c <__sseek>:
   1270c:	ff010113          	addi	sp,sp,-16
   12710:	00812423          	sw	s0,8(sp)
   12714:	00058413          	mv	s0,a1
   12718:	00e59583          	lh	a1,14(a1)
   1271c:	00112623          	sw	ra,12(sp)
   12720:	395000ef          	jal	ra,132b4 <_lseek_r>
   12724:	fff00793          	li	a5,-1
   12728:	02f50463          	beq	a0,a5,12750 <__sseek+0x44>
   1272c:	00c45783          	lhu	a5,12(s0)
   12730:	00001737          	lui	a4,0x1
   12734:	00c12083          	lw	ra,12(sp)
   12738:	00e7e7b3          	or	a5,a5,a4
   1273c:	04a42823          	sw	a0,80(s0)
   12740:	00f41623          	sh	a5,12(s0)
   12744:	00812403          	lw	s0,8(sp)
   12748:	01010113          	addi	sp,sp,16
   1274c:	00008067          	ret
   12750:	00c45783          	lhu	a5,12(s0)
   12754:	fffff737          	lui	a4,0xfffff
   12758:	fff70713          	addi	a4,a4,-1 # ffffefff <__BSS_END__+0xfffe73fb>
   1275c:	00e7f7b3          	and	a5,a5,a4
   12760:	00c12083          	lw	ra,12(sp)
   12764:	00f41623          	sh	a5,12(s0)
   12768:	00812403          	lw	s0,8(sp)
   1276c:	01010113          	addi	sp,sp,16
   12770:	00008067          	ret

00012774 <__sclose>:
   12774:	00e59583          	lh	a1,14(a1)
   12778:	2600006f          	j	129d8 <_close_r>

0001277c <_write_r>:
   1277c:	ff010113          	addi	sp,sp,-16
   12780:	00058713          	mv	a4,a1
   12784:	00812423          	sw	s0,8(sp)
   12788:	00060593          	mv	a1,a2
   1278c:	00050413          	mv	s0,a0
   12790:	00068613          	mv	a2,a3
   12794:	00070513          	mv	a0,a4
   12798:	0401a823          	sw	zero,80(gp) # 17bb8 <errno>
   1279c:	00112623          	sw	ra,12(sp)
   127a0:	2a8010ef          	jal	ra,13a48 <_write>
   127a4:	fff00793          	li	a5,-1
   127a8:	00f50a63          	beq	a0,a5,127bc <_write_r+0x40>
   127ac:	00c12083          	lw	ra,12(sp)
   127b0:	00812403          	lw	s0,8(sp)
   127b4:	01010113          	addi	sp,sp,16
   127b8:	00008067          	ret
   127bc:	0501a783          	lw	a5,80(gp) # 17bb8 <errno>
   127c0:	fe0786e3          	beqz	a5,127ac <_write_r+0x30>
   127c4:	00c12083          	lw	ra,12(sp)
   127c8:	00f42023          	sw	a5,0(s0)
   127cc:	00812403          	lw	s0,8(sp)
   127d0:	01010113          	addi	sp,sp,16
   127d4:	00008067          	ret

000127d8 <__swsetup_r>:
   127d8:	ff010113          	addi	sp,sp,-16
   127dc:	00812423          	sw	s0,8(sp)
   127e0:	00912223          	sw	s1,4(sp)
   127e4:	00112623          	sw	ra,12(sp)
   127e8:	0381a783          	lw	a5,56(gp) # 17ba0 <_impure_ptr>
   127ec:	00050493          	mv	s1,a0
   127f0:	00058413          	mv	s0,a1
   127f4:	00078663          	beqz	a5,12800 <__swsetup_r+0x28>
   127f8:	0387a703          	lw	a4,56(a5)
   127fc:	08070463          	beqz	a4,12884 <__swsetup_r+0xac>
   12800:	00c41703          	lh	a4,12(s0)
   12804:	01071793          	slli	a5,a4,0x10
   12808:	00877693          	andi	a3,a4,8
   1280c:	0107d793          	srli	a5,a5,0x10
   12810:	08068863          	beqz	a3,128a0 <__swsetup_r+0xc8>
   12814:	01042683          	lw	a3,16(s0)
   12818:	0a068863          	beqz	a3,128c8 <__swsetup_r+0xf0>
   1281c:	0017f613          	andi	a2,a5,1
   12820:	02060863          	beqz	a2,12850 <__swsetup_r+0x78>
   12824:	01442603          	lw	a2,20(s0)
   12828:	00042423          	sw	zero,8(s0)
   1282c:	00000513          	li	a0,0
   12830:	40c00633          	neg	a2,a2
   12834:	00c42c23          	sw	a2,24(s0)
   12838:	02068a63          	beqz	a3,1286c <__swsetup_r+0x94>
   1283c:	00c12083          	lw	ra,12(sp)
   12840:	00812403          	lw	s0,8(sp)
   12844:	00412483          	lw	s1,4(sp)
   12848:	01010113          	addi	sp,sp,16
   1284c:	00008067          	ret
   12850:	0027f613          	andi	a2,a5,2
   12854:	00000593          	li	a1,0
   12858:	00061463          	bnez	a2,12860 <__swsetup_r+0x88>
   1285c:	01442583          	lw	a1,20(s0)
   12860:	00b42423          	sw	a1,8(s0)
   12864:	00000513          	li	a0,0
   12868:	fc069ae3          	bnez	a3,1283c <__swsetup_r+0x64>
   1286c:	0807f793          	andi	a5,a5,128
   12870:	fc0786e3          	beqz	a5,1283c <__swsetup_r+0x64>
   12874:	04076713          	ori	a4,a4,64
   12878:	00e41623          	sh	a4,12(s0)
   1287c:	fff00513          	li	a0,-1
   12880:	fbdff06f          	j	1283c <__swsetup_r+0x64>
   12884:	00078513          	mv	a0,a5
   12888:	e90fe0ef          	jal	ra,10f18 <__sinit>
   1288c:	00c41703          	lh	a4,12(s0)
   12890:	01071793          	slli	a5,a4,0x10
   12894:	00877693          	andi	a3,a4,8
   12898:	0107d793          	srli	a5,a5,0x10
   1289c:	f6069ce3          	bnez	a3,12814 <__swsetup_r+0x3c>
   128a0:	0107f693          	andi	a3,a5,16
   128a4:	08068263          	beqz	a3,12928 <__swsetup_r+0x150>
   128a8:	0047f793          	andi	a5,a5,4
   128ac:	04079463          	bnez	a5,128f4 <__swsetup_r+0x11c>
   128b0:	01042683          	lw	a3,16(s0)
   128b4:	00876713          	ori	a4,a4,8
   128b8:	01071793          	slli	a5,a4,0x10
   128bc:	00e41623          	sh	a4,12(s0)
   128c0:	0107d793          	srli	a5,a5,0x10
   128c4:	f4069ce3          	bnez	a3,1281c <__swsetup_r+0x44>
   128c8:	2807f613          	andi	a2,a5,640
   128cc:	20000593          	li	a1,512
   128d0:	f4b606e3          	beq	a2,a1,1281c <__swsetup_r+0x44>
   128d4:	00040593          	mv	a1,s0
   128d8:	00048513          	mv	a0,s1
   128dc:	235000ef          	jal	ra,13310 <__smakebuf_r>
   128e0:	00c41703          	lh	a4,12(s0)
   128e4:	01042683          	lw	a3,16(s0)
   128e8:	01071793          	slli	a5,a4,0x10
   128ec:	0107d793          	srli	a5,a5,0x10
   128f0:	f2dff06f          	j	1281c <__swsetup_r+0x44>
   128f4:	03042583          	lw	a1,48(s0)
   128f8:	00058e63          	beqz	a1,12914 <__swsetup_r+0x13c>
   128fc:	04040793          	addi	a5,s0,64
   12900:	00f58863          	beq	a1,a5,12910 <__swsetup_r+0x138>
   12904:	00048513          	mv	a0,s1
   12908:	6ac000ef          	jal	ra,12fb4 <_free_r>
   1290c:	00c41703          	lh	a4,12(s0)
   12910:	02042823          	sw	zero,48(s0)
   12914:	01042683          	lw	a3,16(s0)
   12918:	fdb77713          	andi	a4,a4,-37
   1291c:	00042223          	sw	zero,4(s0)
   12920:	00d42023          	sw	a3,0(s0)
   12924:	f91ff06f          	j	128b4 <__swsetup_r+0xdc>
   12928:	00900793          	li	a5,9
   1292c:	00f4a023          	sw	a5,0(s1)
   12930:	04076713          	ori	a4,a4,64
   12934:	00e41623          	sh	a4,12(s0)
   12938:	fff00513          	li	a0,-1
   1293c:	f01ff06f          	j	1283c <__swsetup_r+0x64>

00012940 <__register_exitproc>:
   12940:	0301a703          	lw	a4,48(gp) # 17b98 <_global_impure_ptr>
   12944:	14872783          	lw	a5,328(a4)
   12948:	04078c63          	beqz	a5,129a0 <__register_exitproc+0x60>
   1294c:	0047a703          	lw	a4,4(a5)
   12950:	01f00813          	li	a6,31
   12954:	06e84e63          	blt	a6,a4,129d0 <__register_exitproc+0x90>
   12958:	00271813          	slli	a6,a4,0x2
   1295c:	02050663          	beqz	a0,12988 <__register_exitproc+0x48>
   12960:	01078333          	add	t1,a5,a6
   12964:	08c32423          	sw	a2,136(t1)
   12968:	1887a883          	lw	a7,392(a5)
   1296c:	00100613          	li	a2,1
   12970:	00e61633          	sll	a2,a2,a4
   12974:	00c8e8b3          	or	a7,a7,a2
   12978:	1917a423          	sw	a7,392(a5)
   1297c:	10d32423          	sw	a3,264(t1)
   12980:	00200693          	li	a3,2
   12984:	02d50463          	beq	a0,a3,129ac <__register_exitproc+0x6c>
   12988:	00170713          	addi	a4,a4,1
   1298c:	00e7a223          	sw	a4,4(a5)
   12990:	010787b3          	add	a5,a5,a6
   12994:	00b7a423          	sw	a1,8(a5)
   12998:	00000513          	li	a0,0
   1299c:	00008067          	ret
   129a0:	14c70793          	addi	a5,a4,332
   129a4:	14f72423          	sw	a5,328(a4)
   129a8:	fa5ff06f          	j	1294c <__register_exitproc+0xc>
   129ac:	18c7a683          	lw	a3,396(a5)
   129b0:	00170713          	addi	a4,a4,1
   129b4:	00e7a223          	sw	a4,4(a5)
   129b8:	00c6e6b3          	or	a3,a3,a2
   129bc:	18d7a623          	sw	a3,396(a5)
   129c0:	010787b3          	add	a5,a5,a6
   129c4:	00b7a423          	sw	a1,8(a5)
   129c8:	00000513          	li	a0,0
   129cc:	00008067          	ret
   129d0:	fff00513          	li	a0,-1
   129d4:	00008067          	ret

000129d8 <_close_r>:
   129d8:	ff010113          	addi	sp,sp,-16
   129dc:	00812423          	sw	s0,8(sp)
   129e0:	00050413          	mv	s0,a0
   129e4:	00058513          	mv	a0,a1
   129e8:	0401a823          	sw	zero,80(gp) # 17bb8 <errno>
   129ec:	00112623          	sw	ra,12(sp)
   129f0:	641000ef          	jal	ra,13830 <_close>
   129f4:	fff00793          	li	a5,-1
   129f8:	00f50a63          	beq	a0,a5,12a0c <_close_r+0x34>
   129fc:	00c12083          	lw	ra,12(sp)
   12a00:	00812403          	lw	s0,8(sp)
   12a04:	01010113          	addi	sp,sp,16
   12a08:	00008067          	ret
   12a0c:	0501a783          	lw	a5,80(gp) # 17bb8 <errno>
   12a10:	fe0786e3          	beqz	a5,129fc <_close_r+0x24>
   12a14:	00c12083          	lw	ra,12(sp)
   12a18:	00f42023          	sw	a5,0(s0)
   12a1c:	00812403          	lw	s0,8(sp)
   12a20:	01010113          	addi	sp,sp,16
   12a24:	00008067          	ret

00012a28 <_fclose_r>:
   12a28:	ff010113          	addi	sp,sp,-16
   12a2c:	00112623          	sw	ra,12(sp)
   12a30:	00812423          	sw	s0,8(sp)
   12a34:	00912223          	sw	s1,4(sp)
   12a38:	01212023          	sw	s2,0(sp)
   12a3c:	02058063          	beqz	a1,12a5c <_fclose_r+0x34>
   12a40:	00058413          	mv	s0,a1
   12a44:	00050493          	mv	s1,a0
   12a48:	00050663          	beqz	a0,12a54 <_fclose_r+0x2c>
   12a4c:	03852783          	lw	a5,56(a0)
   12a50:	0a078c63          	beqz	a5,12b08 <_fclose_r+0xe0>
   12a54:	00c41783          	lh	a5,12(s0)
   12a58:	02079263          	bnez	a5,12a7c <_fclose_r+0x54>
   12a5c:	00c12083          	lw	ra,12(sp)
   12a60:	00812403          	lw	s0,8(sp)
   12a64:	00000913          	li	s2,0
   12a68:	00412483          	lw	s1,4(sp)
   12a6c:	00090513          	mv	a0,s2
   12a70:	00012903          	lw	s2,0(sp)
   12a74:	01010113          	addi	sp,sp,16
   12a78:	00008067          	ret
   12a7c:	00040593          	mv	a1,s0
   12a80:	00048513          	mv	a0,s1
   12a84:	0c0000ef          	jal	ra,12b44 <__sflush_r>
   12a88:	02c42783          	lw	a5,44(s0)
   12a8c:	00050913          	mv	s2,a0
   12a90:	00078a63          	beqz	a5,12aa4 <_fclose_r+0x7c>
   12a94:	01c42583          	lw	a1,28(s0)
   12a98:	00048513          	mv	a0,s1
   12a9c:	000780e7          	jalr	a5
   12aa0:	06054c63          	bltz	a0,12b18 <_fclose_r+0xf0>
   12aa4:	00c45783          	lhu	a5,12(s0)
   12aa8:	0807f793          	andi	a5,a5,128
   12aac:	06079e63          	bnez	a5,12b28 <_fclose_r+0x100>
   12ab0:	03042583          	lw	a1,48(s0)
   12ab4:	00058c63          	beqz	a1,12acc <_fclose_r+0xa4>
   12ab8:	04040793          	addi	a5,s0,64
   12abc:	00f58663          	beq	a1,a5,12ac8 <_fclose_r+0xa0>
   12ac0:	00048513          	mv	a0,s1
   12ac4:	4f0000ef          	jal	ra,12fb4 <_free_r>
   12ac8:	02042823          	sw	zero,48(s0)
   12acc:	04442583          	lw	a1,68(s0)
   12ad0:	00058863          	beqz	a1,12ae0 <_fclose_r+0xb8>
   12ad4:	00048513          	mv	a0,s1
   12ad8:	4dc000ef          	jal	ra,12fb4 <_free_r>
   12adc:	04042223          	sw	zero,68(s0)
   12ae0:	c48fe0ef          	jal	ra,10f28 <__sfp_lock_acquire>
   12ae4:	00041623          	sh	zero,12(s0)
   12ae8:	c44fe0ef          	jal	ra,10f2c <__sfp_lock_release>
   12aec:	00c12083          	lw	ra,12(sp)
   12af0:	00812403          	lw	s0,8(sp)
   12af4:	00412483          	lw	s1,4(sp)
   12af8:	00090513          	mv	a0,s2
   12afc:	00012903          	lw	s2,0(sp)
   12b00:	01010113          	addi	sp,sp,16
   12b04:	00008067          	ret
   12b08:	c10fe0ef          	jal	ra,10f18 <__sinit>
   12b0c:	00c41783          	lh	a5,12(s0)
   12b10:	f40786e3          	beqz	a5,12a5c <_fclose_r+0x34>
   12b14:	f69ff06f          	j	12a7c <_fclose_r+0x54>
   12b18:	00c45783          	lhu	a5,12(s0)
   12b1c:	fff00913          	li	s2,-1
   12b20:	0807f793          	andi	a5,a5,128
   12b24:	f80786e3          	beqz	a5,12ab0 <_fclose_r+0x88>
   12b28:	01042583          	lw	a1,16(s0)
   12b2c:	00048513          	mv	a0,s1
   12b30:	484000ef          	jal	ra,12fb4 <_free_r>
   12b34:	f7dff06f          	j	12ab0 <_fclose_r+0x88>

00012b38 <fclose>:
   12b38:	00050593          	mv	a1,a0
   12b3c:	0381a503          	lw	a0,56(gp) # 17ba0 <_impure_ptr>
   12b40:	ee9ff06f          	j	12a28 <_fclose_r>

00012b44 <__sflush_r>:
   12b44:	00c59783          	lh	a5,12(a1)
   12b48:	fe010113          	addi	sp,sp,-32
   12b4c:	00812c23          	sw	s0,24(sp)
   12b50:	01312623          	sw	s3,12(sp)
   12b54:	00112e23          	sw	ra,28(sp)
   12b58:	00912a23          	sw	s1,20(sp)
   12b5c:	01212823          	sw	s2,16(sp)
   12b60:	0087f693          	andi	a3,a5,8
   12b64:	00058413          	mv	s0,a1
   12b68:	00050993          	mv	s3,a0
   12b6c:	10069c63          	bnez	a3,12c84 <__sflush_r+0x140>
   12b70:	00001737          	lui	a4,0x1
   12b74:	80070713          	addi	a4,a4,-2048 # 800 <main-0xf874>
   12b78:	0045a683          	lw	a3,4(a1)
   12b7c:	00e7e7b3          	or	a5,a5,a4
   12b80:	00f59623          	sh	a5,12(a1)
   12b84:	18d05663          	blez	a3,12d10 <__sflush_r+0x1cc>
   12b88:	02842703          	lw	a4,40(s0)
   12b8c:	0c070c63          	beqz	a4,12c64 <__sflush_r+0x120>
   12b90:	01079793          	slli	a5,a5,0x10
   12b94:	0107d793          	srli	a5,a5,0x10
   12b98:	000016b7          	lui	a3,0x1
   12b9c:	0009a483          	lw	s1,0(s3)
   12ba0:	00d7f6b3          	and	a3,a5,a3
   12ba4:	0009a023          	sw	zero,0(s3)
   12ba8:	01c42583          	lw	a1,28(s0)
   12bac:	16069863          	bnez	a3,12d1c <__sflush_r+0x1d8>
   12bb0:	00100693          	li	a3,1
   12bb4:	00000613          	li	a2,0
   12bb8:	00098513          	mv	a0,s3
   12bbc:	000700e7          	jalr	a4
   12bc0:	fff00793          	li	a5,-1
   12bc4:	18f50e63          	beq	a0,a5,12d60 <__sflush_r+0x21c>
   12bc8:	00c45783          	lhu	a5,12(s0)
   12bcc:	02842703          	lw	a4,40(s0)
   12bd0:	01c42583          	lw	a1,28(s0)
   12bd4:	0047f793          	andi	a5,a5,4
   12bd8:	00078e63          	beqz	a5,12bf4 <__sflush_r+0xb0>
   12bdc:	00442683          	lw	a3,4(s0)
   12be0:	03042783          	lw	a5,48(s0)
   12be4:	40d50533          	sub	a0,a0,a3
   12be8:	00078663          	beqz	a5,12bf4 <__sflush_r+0xb0>
   12bec:	03c42783          	lw	a5,60(s0)
   12bf0:	40f50533          	sub	a0,a0,a5
   12bf4:	00050613          	mv	a2,a0
   12bf8:	00000693          	li	a3,0
   12bfc:	00098513          	mv	a0,s3
   12c00:	000700e7          	jalr	a4
   12c04:	fff00793          	li	a5,-1
   12c08:	10f51e63          	bne	a0,a5,12d24 <__sflush_r+0x1e0>
   12c0c:	0009a703          	lw	a4,0(s3)
   12c10:	00c41783          	lh	a5,12(s0)
   12c14:	16070a63          	beqz	a4,12d88 <__sflush_r+0x244>
   12c18:	01d00693          	li	a3,29
   12c1c:	00d70663          	beq	a4,a3,12c28 <__sflush_r+0xe4>
   12c20:	01600693          	li	a3,22
   12c24:	0cd71463          	bne	a4,a3,12cec <__sflush_r+0x1a8>
   12c28:	01042683          	lw	a3,16(s0)
   12c2c:	fffff737          	lui	a4,0xfffff
   12c30:	7ff70713          	addi	a4,a4,2047 # fffff7ff <__BSS_END__+0xfffe7bfb>
   12c34:	00e7f7b3          	and	a5,a5,a4
   12c38:	00f41623          	sh	a5,12(s0)
   12c3c:	00042223          	sw	zero,4(s0)
   12c40:	00d42023          	sw	a3,0(s0)
   12c44:	03042583          	lw	a1,48(s0)
   12c48:	0099a023          	sw	s1,0(s3)
   12c4c:	00058c63          	beqz	a1,12c64 <__sflush_r+0x120>
   12c50:	04040793          	addi	a5,s0,64
   12c54:	00f58663          	beq	a1,a5,12c60 <__sflush_r+0x11c>
   12c58:	00098513          	mv	a0,s3
   12c5c:	358000ef          	jal	ra,12fb4 <_free_r>
   12c60:	02042823          	sw	zero,48(s0)
   12c64:	00000513          	li	a0,0
   12c68:	01c12083          	lw	ra,28(sp)
   12c6c:	01812403          	lw	s0,24(sp)
   12c70:	01412483          	lw	s1,20(sp)
   12c74:	01012903          	lw	s2,16(sp)
   12c78:	00c12983          	lw	s3,12(sp)
   12c7c:	02010113          	addi	sp,sp,32
   12c80:	00008067          	ret
   12c84:	0105a903          	lw	s2,16(a1)
   12c88:	fc090ee3          	beqz	s2,12c64 <__sflush_r+0x120>
   12c8c:	0005a483          	lw	s1,0(a1)
   12c90:	01079713          	slli	a4,a5,0x10
   12c94:	01075713          	srli	a4,a4,0x10
   12c98:	00377713          	andi	a4,a4,3
   12c9c:	0125a023          	sw	s2,0(a1)
   12ca0:	412484b3          	sub	s1,s1,s2
   12ca4:	00000793          	li	a5,0
   12ca8:	00071463          	bnez	a4,12cb0 <__sflush_r+0x16c>
   12cac:	0145a783          	lw	a5,20(a1)
   12cb0:	00f42423          	sw	a5,8(s0)
   12cb4:	00904863          	bgtz	s1,12cc4 <__sflush_r+0x180>
   12cb8:	fadff06f          	j	12c64 <__sflush_r+0x120>
   12cbc:	00a90933          	add	s2,s2,a0
   12cc0:	fa9052e3          	blez	s1,12c64 <__sflush_r+0x120>
   12cc4:	02442783          	lw	a5,36(s0)
   12cc8:	01c42583          	lw	a1,28(s0)
   12ccc:	00048693          	mv	a3,s1
   12cd0:	00090613          	mv	a2,s2
   12cd4:	00098513          	mv	a0,s3
   12cd8:	000780e7          	jalr	a5
   12cdc:	40a484b3          	sub	s1,s1,a0
   12ce0:	fca04ee3          	bgtz	a0,12cbc <__sflush_r+0x178>
   12ce4:	00c45783          	lhu	a5,12(s0)
   12ce8:	fff00513          	li	a0,-1
   12cec:	0407e793          	ori	a5,a5,64
   12cf0:	01c12083          	lw	ra,28(sp)
   12cf4:	00f41623          	sh	a5,12(s0)
   12cf8:	01812403          	lw	s0,24(sp)
   12cfc:	01412483          	lw	s1,20(sp)
   12d00:	01012903          	lw	s2,16(sp)
   12d04:	00c12983          	lw	s3,12(sp)
   12d08:	02010113          	addi	sp,sp,32
   12d0c:	00008067          	ret
   12d10:	03c5a703          	lw	a4,60(a1)
   12d14:	e6e04ae3          	bgtz	a4,12b88 <__sflush_r+0x44>
   12d18:	f4dff06f          	j	12c64 <__sflush_r+0x120>
   12d1c:	05042503          	lw	a0,80(s0)
   12d20:	eb5ff06f          	j	12bd4 <__sflush_r+0x90>
   12d24:	00c45783          	lhu	a5,12(s0)
   12d28:	fffff737          	lui	a4,0xfffff
   12d2c:	7ff70713          	addi	a4,a4,2047 # fffff7ff <__BSS_END__+0xfffe7bfb>
   12d30:	00e7f7b3          	and	a5,a5,a4
   12d34:	01042683          	lw	a3,16(s0)
   12d38:	01079793          	slli	a5,a5,0x10
   12d3c:	4107d793          	srai	a5,a5,0x10
   12d40:	00c7d713          	srli	a4,a5,0xc
   12d44:	00f41623          	sh	a5,12(s0)
   12d48:	00042223          	sw	zero,4(s0)
   12d4c:	00d42023          	sw	a3,0(s0)
   12d50:	00177793          	andi	a5,a4,1
   12d54:	ee0788e3          	beqz	a5,12c44 <__sflush_r+0x100>
   12d58:	04a42823          	sw	a0,80(s0)
   12d5c:	ee9ff06f          	j	12c44 <__sflush_r+0x100>
   12d60:	0009a783          	lw	a5,0(s3)
   12d64:	e60782e3          	beqz	a5,12bc8 <__sflush_r+0x84>
   12d68:	01d00713          	li	a4,29
   12d6c:	02e78863          	beq	a5,a4,12d9c <__sflush_r+0x258>
   12d70:	01600713          	li	a4,22
   12d74:	02e78463          	beq	a5,a4,12d9c <__sflush_r+0x258>
   12d78:	00c45783          	lhu	a5,12(s0)
   12d7c:	0407e793          	ori	a5,a5,64
   12d80:	00f41623          	sh	a5,12(s0)
   12d84:	ee5ff06f          	j	12c68 <__sflush_r+0x124>
   12d88:	fffff737          	lui	a4,0xfffff
   12d8c:	7ff70713          	addi	a4,a4,2047 # fffff7ff <__BSS_END__+0xfffe7bfb>
   12d90:	01042683          	lw	a3,16(s0)
   12d94:	00e7f7b3          	and	a5,a5,a4
   12d98:	fa9ff06f          	j	12d40 <__sflush_r+0x1fc>
   12d9c:	0099a023          	sw	s1,0(s3)
   12da0:	00000513          	li	a0,0
   12da4:	ec5ff06f          	j	12c68 <__sflush_r+0x124>

00012da8 <_fflush_r>:
   12da8:	fe010113          	addi	sp,sp,-32
   12dac:	00812c23          	sw	s0,24(sp)
   12db0:	00112e23          	sw	ra,28(sp)
   12db4:	00050413          	mv	s0,a0
   12db8:	00050663          	beqz	a0,12dc4 <_fflush_r+0x1c>
   12dbc:	03852783          	lw	a5,56(a0)
   12dc0:	02078063          	beqz	a5,12de0 <_fflush_r+0x38>
   12dc4:	00c59783          	lh	a5,12(a1)
   12dc8:	02079663          	bnez	a5,12df4 <_fflush_r+0x4c>
   12dcc:	01c12083          	lw	ra,28(sp)
   12dd0:	01812403          	lw	s0,24(sp)
   12dd4:	00000513          	li	a0,0
   12dd8:	02010113          	addi	sp,sp,32
   12ddc:	00008067          	ret
   12de0:	00b12623          	sw	a1,12(sp)
   12de4:	934fe0ef          	jal	ra,10f18 <__sinit>
   12de8:	00c12583          	lw	a1,12(sp)
   12dec:	00c59783          	lh	a5,12(a1)
   12df0:	fc078ee3          	beqz	a5,12dcc <_fflush_r+0x24>
   12df4:	00040513          	mv	a0,s0
   12df8:	01812403          	lw	s0,24(sp)
   12dfc:	01c12083          	lw	ra,28(sp)
   12e00:	02010113          	addi	sp,sp,32
   12e04:	d41ff06f          	j	12b44 <__sflush_r>

00012e08 <fflush>:
   12e08:	06050663          	beqz	a0,12e74 <fflush+0x6c>
   12e0c:	fe010113          	addi	sp,sp,-32
   12e10:	00812c23          	sw	s0,24(sp)
   12e14:	00112e23          	sw	ra,28(sp)
   12e18:	00050413          	mv	s0,a0
   12e1c:	0381a503          	lw	a0,56(gp) # 17ba0 <_impure_ptr>
   12e20:	00050663          	beqz	a0,12e2c <fflush+0x24>
   12e24:	03852783          	lw	a5,56(a0)
   12e28:	02078a63          	beqz	a5,12e5c <fflush+0x54>
   12e2c:	00c41783          	lh	a5,12(s0)
   12e30:	00079c63          	bnez	a5,12e48 <fflush+0x40>
   12e34:	01c12083          	lw	ra,28(sp)
   12e38:	01812403          	lw	s0,24(sp)
   12e3c:	00000513          	li	a0,0
   12e40:	02010113          	addi	sp,sp,32
   12e44:	00008067          	ret
   12e48:	00040593          	mv	a1,s0
   12e4c:	01812403          	lw	s0,24(sp)
   12e50:	01c12083          	lw	ra,28(sp)
   12e54:	02010113          	addi	sp,sp,32
   12e58:	cedff06f          	j	12b44 <__sflush_r>
   12e5c:	00a12623          	sw	a0,12(sp)
   12e60:	8b8fe0ef          	jal	ra,10f18 <__sinit>
   12e64:	00c41783          	lh	a5,12(s0)
   12e68:	00c12503          	lw	a0,12(sp)
   12e6c:	fc0784e3          	beqz	a5,12e34 <fflush+0x2c>
   12e70:	fd9ff06f          	j	12e48 <fflush+0x40>
   12e74:	00000597          	auipc	a1,0x0
   12e78:	f3458593          	addi	a1,a1,-204 # 12da8 <_fflush_r>
   12e7c:	0301a503          	lw	a0,48(gp) # 17b98 <_global_impure_ptr>
   12e80:	e88fe06f          	j	11508 <_fwalk_reent>

00012e84 <_malloc_trim_r>:
   12e84:	fe010113          	addi	sp,sp,-32
   12e88:	00812c23          	sw	s0,24(sp)
   12e8c:	00912a23          	sw	s1,20(sp)
   12e90:	01212823          	sw	s2,16(sp)
   12e94:	01312623          	sw	s3,12(sp)
   12e98:	01412423          	sw	s4,8(sp)
   12e9c:	00058993          	mv	s3,a1
   12ea0:	00112e23          	sw	ra,28(sp)
   12ea4:	c2818a13          	addi	s4,gp,-984 # 17790 <__malloc_av_>
   12ea8:	00050913          	mv	s2,a0
   12eac:	9c4ff0ef          	jal	ra,12070 <__malloc_lock>
   12eb0:	008a2703          	lw	a4,8(s4)
   12eb4:	000017b7          	lui	a5,0x1
   12eb8:	fef78413          	addi	s0,a5,-17 # fef <main-0xf085>
   12ebc:	00472483          	lw	s1,4(a4)
   12ec0:	41340433          	sub	s0,s0,s3
   12ec4:	ffc4f493          	andi	s1,s1,-4
   12ec8:	00940433          	add	s0,s0,s1
   12ecc:	00c45413          	srli	s0,s0,0xc
   12ed0:	fff40413          	addi	s0,s0,-1
   12ed4:	00c41413          	slli	s0,s0,0xc
   12ed8:	00f44e63          	blt	s0,a5,12ef4 <_malloc_trim_r+0x70>
   12edc:	00000593          	li	a1,0
   12ee0:	00090513          	mv	a0,s2
   12ee4:	eecff0ef          	jal	ra,125d0 <_sbrk_r>
   12ee8:	008a2783          	lw	a5,8(s4)
   12eec:	009787b3          	add	a5,a5,s1
   12ef0:	02f50863          	beq	a0,a5,12f20 <_malloc_trim_r+0x9c>
   12ef4:	00090513          	mv	a0,s2
   12ef8:	97cff0ef          	jal	ra,12074 <__malloc_unlock>
   12efc:	01c12083          	lw	ra,28(sp)
   12f00:	01812403          	lw	s0,24(sp)
   12f04:	01412483          	lw	s1,20(sp)
   12f08:	01012903          	lw	s2,16(sp)
   12f0c:	00c12983          	lw	s3,12(sp)
   12f10:	00812a03          	lw	s4,8(sp)
   12f14:	00000513          	li	a0,0
   12f18:	02010113          	addi	sp,sp,32
   12f1c:	00008067          	ret
   12f20:	408005b3          	neg	a1,s0
   12f24:	00090513          	mv	a0,s2
   12f28:	ea8ff0ef          	jal	ra,125d0 <_sbrk_r>
   12f2c:	fff00793          	li	a5,-1
   12f30:	04f50863          	beq	a0,a5,12f80 <_malloc_trim_r+0xfc>
   12f34:	07418713          	addi	a4,gp,116 # 17bdc <__malloc_current_mallinfo>
   12f38:	00072783          	lw	a5,0(a4)
   12f3c:	008a2683          	lw	a3,8(s4)
   12f40:	408484b3          	sub	s1,s1,s0
   12f44:	0014e493          	ori	s1,s1,1
   12f48:	408787b3          	sub	a5,a5,s0
   12f4c:	00090513          	mv	a0,s2
   12f50:	0096a223          	sw	s1,4(a3) # 1004 <main-0xf070>
   12f54:	00f72023          	sw	a5,0(a4)
   12f58:	91cff0ef          	jal	ra,12074 <__malloc_unlock>
   12f5c:	01c12083          	lw	ra,28(sp)
   12f60:	01812403          	lw	s0,24(sp)
   12f64:	01412483          	lw	s1,20(sp)
   12f68:	01012903          	lw	s2,16(sp)
   12f6c:	00c12983          	lw	s3,12(sp)
   12f70:	00812a03          	lw	s4,8(sp)
   12f74:	00100513          	li	a0,1
   12f78:	02010113          	addi	sp,sp,32
   12f7c:	00008067          	ret
   12f80:	00000593          	li	a1,0
   12f84:	00090513          	mv	a0,s2
   12f88:	e48ff0ef          	jal	ra,125d0 <_sbrk_r>
   12f8c:	008a2703          	lw	a4,8(s4)
   12f90:	00f00693          	li	a3,15
   12f94:	40e507b3          	sub	a5,a0,a4
   12f98:	f4f6dee3          	bge	a3,a5,12ef4 <_malloc_trim_r+0x70>
   12f9c:	03c1a683          	lw	a3,60(gp) # 17ba4 <__malloc_sbrk_base>
   12fa0:	40d50533          	sub	a0,a0,a3
   12fa4:	0017e793          	ori	a5,a5,1
   12fa8:	06a1aa23          	sw	a0,116(gp) # 17bdc <__malloc_current_mallinfo>
   12fac:	00f72223          	sw	a5,4(a4)
   12fb0:	f45ff06f          	j	12ef4 <_malloc_trim_r+0x70>

00012fb4 <_free_r>:
   12fb4:	12058463          	beqz	a1,130dc <_free_r+0x128>
   12fb8:	ff010113          	addi	sp,sp,-16
   12fbc:	00812423          	sw	s0,8(sp)
   12fc0:	00912223          	sw	s1,4(sp)
   12fc4:	00058413          	mv	s0,a1
   12fc8:	00050493          	mv	s1,a0
   12fcc:	00112623          	sw	ra,12(sp)
   12fd0:	8a0ff0ef          	jal	ra,12070 <__malloc_lock>
   12fd4:	ffc42583          	lw	a1,-4(s0)
   12fd8:	ff840713          	addi	a4,s0,-8
   12fdc:	c2818813          	addi	a6,gp,-984 # 17790 <__malloc_av_>
   12fe0:	ffe5f793          	andi	a5,a1,-2
   12fe4:	00f70633          	add	a2,a4,a5
   12fe8:	00462683          	lw	a3,4(a2)
   12fec:	00882503          	lw	a0,8(a6)
   12ff0:	ffc6f693          	andi	a3,a3,-4
   12ff4:	1ac50663          	beq	a0,a2,131a0 <_free_r+0x1ec>
   12ff8:	00d62223          	sw	a3,4(a2)
   12ffc:	0015f593          	andi	a1,a1,1
   13000:	00d60533          	add	a0,a2,a3
   13004:	08059e63          	bnez	a1,130a0 <_free_r+0xec>
   13008:	ff842303          	lw	t1,-8(s0)
   1300c:	00452583          	lw	a1,4(a0)
   13010:	c3018893          	addi	a7,gp,-976 # 17798 <__malloc_av_+0x8>
   13014:	40670733          	sub	a4,a4,t1
   13018:	00872503          	lw	a0,8(a4)
   1301c:	006787b3          	add	a5,a5,t1
   13020:	0015f593          	andi	a1,a1,1
   13024:	13150e63          	beq	a0,a7,13160 <_free_r+0x1ac>
   13028:	00c72303          	lw	t1,12(a4)
   1302c:	00652623          	sw	t1,12(a0)
   13030:	00a32423          	sw	a0,8(t1)
   13034:	1c058e63          	beqz	a1,13210 <_free_r+0x25c>
   13038:	0017e693          	ori	a3,a5,1
   1303c:	00d72223          	sw	a3,4(a4)
   13040:	00f62023          	sw	a5,0(a2)
   13044:	1ff00693          	li	a3,511
   13048:	0af6e663          	bltu	a3,a5,130f4 <_free_r+0x140>
   1304c:	ff87f693          	andi	a3,a5,-8
   13050:	00868693          	addi	a3,a3,8
   13054:	00482583          	lw	a1,4(a6)
   13058:	00d806b3          	add	a3,a6,a3
   1305c:	0006a603          	lw	a2,0(a3)
   13060:	0057d513          	srli	a0,a5,0x5
   13064:	00100793          	li	a5,1
   13068:	00a797b3          	sll	a5,a5,a0
   1306c:	00b7e7b3          	or	a5,a5,a1
   13070:	ff868593          	addi	a1,a3,-8
   13074:	00b72623          	sw	a1,12(a4)
   13078:	00c72423          	sw	a2,8(a4)
   1307c:	00f82223          	sw	a5,4(a6)
   13080:	00e6a023          	sw	a4,0(a3)
   13084:	00e62623          	sw	a4,12(a2)
   13088:	00812403          	lw	s0,8(sp)
   1308c:	00c12083          	lw	ra,12(sp)
   13090:	00048513          	mv	a0,s1
   13094:	00412483          	lw	s1,4(sp)
   13098:	01010113          	addi	sp,sp,16
   1309c:	fd9fe06f          	j	12074 <__malloc_unlock>
   130a0:	00452583          	lw	a1,4(a0)
   130a4:	0015f593          	andi	a1,a1,1
   130a8:	02059c63          	bnez	a1,130e0 <_free_r+0x12c>
   130ac:	00d787b3          	add	a5,a5,a3
   130b0:	c3018893          	addi	a7,gp,-976 # 17798 <__malloc_av_+0x8>
   130b4:	00862683          	lw	a3,8(a2)
   130b8:	0017e513          	ori	a0,a5,1
   130bc:	00f705b3          	add	a1,a4,a5
   130c0:	17168463          	beq	a3,a7,13228 <_free_r+0x274>
   130c4:	00c62603          	lw	a2,12(a2)
   130c8:	00c6a623          	sw	a2,12(a3)
   130cc:	00d62423          	sw	a3,8(a2)
   130d0:	00a72223          	sw	a0,4(a4)
   130d4:	00f5a023          	sw	a5,0(a1)
   130d8:	f6dff06f          	j	13044 <_free_r+0x90>
   130dc:	00008067          	ret
   130e0:	0017e693          	ori	a3,a5,1
   130e4:	fed42e23          	sw	a3,-4(s0)
   130e8:	00f62023          	sw	a5,0(a2)
   130ec:	1ff00693          	li	a3,511
   130f0:	f4f6fee3          	bgeu	a3,a5,1304c <_free_r+0x98>
   130f4:	0097d693          	srli	a3,a5,0x9
   130f8:	00400613          	li	a2,4
   130fc:	0ed66863          	bltu	a2,a3,131ec <_free_r+0x238>
   13100:	0067d693          	srli	a3,a5,0x6
   13104:	03968593          	addi	a1,a3,57
   13108:	03868613          	addi	a2,a3,56
   1310c:	00359593          	slli	a1,a1,0x3
   13110:	00b805b3          	add	a1,a6,a1
   13114:	0005a683          	lw	a3,0(a1)
   13118:	ff858593          	addi	a1,a1,-8
   1311c:	12d58463          	beq	a1,a3,13244 <_free_r+0x290>
   13120:	0046a603          	lw	a2,4(a3)
   13124:	ffc67613          	andi	a2,a2,-4
   13128:	00c7f663          	bgeu	a5,a2,13134 <_free_r+0x180>
   1312c:	0086a683          	lw	a3,8(a3)
   13130:	fed598e3          	bne	a1,a3,13120 <_free_r+0x16c>
   13134:	00c6a583          	lw	a1,12(a3)
   13138:	00b72623          	sw	a1,12(a4)
   1313c:	00d72423          	sw	a3,8(a4)
   13140:	00812403          	lw	s0,8(sp)
   13144:	00c12083          	lw	ra,12(sp)
   13148:	00e5a423          	sw	a4,8(a1)
   1314c:	00048513          	mv	a0,s1
   13150:	00412483          	lw	s1,4(sp)
   13154:	00e6a623          	sw	a4,12(a3)
   13158:	01010113          	addi	sp,sp,16
   1315c:	f19fe06f          	j	12074 <__malloc_unlock>
   13160:	14059263          	bnez	a1,132a4 <_free_r+0x2f0>
   13164:	00c62583          	lw	a1,12(a2)
   13168:	00862603          	lw	a2,8(a2)
   1316c:	00f686b3          	add	a3,a3,a5
   13170:	00812403          	lw	s0,8(sp)
   13174:	00b62623          	sw	a1,12(a2)
   13178:	00c5a423          	sw	a2,8(a1)
   1317c:	0016e793          	ori	a5,a3,1
   13180:	00c12083          	lw	ra,12(sp)
   13184:	00f72223          	sw	a5,4(a4)
   13188:	00048513          	mv	a0,s1
   1318c:	00d70733          	add	a4,a4,a3
   13190:	00412483          	lw	s1,4(sp)
   13194:	00d72023          	sw	a3,0(a4)
   13198:	01010113          	addi	sp,sp,16
   1319c:	ed9fe06f          	j	12074 <__malloc_unlock>
   131a0:	0015f593          	andi	a1,a1,1
   131a4:	00d786b3          	add	a3,a5,a3
   131a8:	02059063          	bnez	a1,131c8 <_free_r+0x214>
   131ac:	ff842583          	lw	a1,-8(s0)
   131b0:	40b70733          	sub	a4,a4,a1
   131b4:	00c72783          	lw	a5,12(a4)
   131b8:	00872603          	lw	a2,8(a4)
   131bc:	00b686b3          	add	a3,a3,a1
   131c0:	00f62623          	sw	a5,12(a2)
   131c4:	00c7a423          	sw	a2,8(a5)
   131c8:	0016e793          	ori	a5,a3,1
   131cc:	00f72223          	sw	a5,4(a4)
   131d0:	00e82423          	sw	a4,8(a6)
   131d4:	0401a783          	lw	a5,64(gp) # 17ba8 <__malloc_trim_threshold>
   131d8:	eaf6e8e3          	bltu	a3,a5,13088 <_free_r+0xd4>
   131dc:	04c1a583          	lw	a1,76(gp) # 17bb4 <__malloc_top_pad>
   131e0:	00048513          	mv	a0,s1
   131e4:	ca1ff0ef          	jal	ra,12e84 <_malloc_trim_r>
   131e8:	ea1ff06f          	j	13088 <_free_r+0xd4>
   131ec:	01400613          	li	a2,20
   131f0:	02d67463          	bgeu	a2,a3,13218 <_free_r+0x264>
   131f4:	05400613          	li	a2,84
   131f8:	06d66463          	bltu	a2,a3,13260 <_free_r+0x2ac>
   131fc:	00c7d693          	srli	a3,a5,0xc
   13200:	06f68593          	addi	a1,a3,111
   13204:	06e68613          	addi	a2,a3,110
   13208:	00359593          	slli	a1,a1,0x3
   1320c:	f05ff06f          	j	13110 <_free_r+0x15c>
   13210:	00d787b3          	add	a5,a5,a3
   13214:	ea1ff06f          	j	130b4 <_free_r+0x100>
   13218:	05c68593          	addi	a1,a3,92
   1321c:	05b68613          	addi	a2,a3,91
   13220:	00359593          	slli	a1,a1,0x3
   13224:	eedff06f          	j	13110 <_free_r+0x15c>
   13228:	00e82a23          	sw	a4,20(a6)
   1322c:	00e82823          	sw	a4,16(a6)
   13230:	01172623          	sw	a7,12(a4)
   13234:	01172423          	sw	a7,8(a4)
   13238:	00a72223          	sw	a0,4(a4)
   1323c:	00f5a023          	sw	a5,0(a1)
   13240:	e49ff06f          	j	13088 <_free_r+0xd4>
   13244:	00482503          	lw	a0,4(a6)
   13248:	40265613          	srai	a2,a2,0x2
   1324c:	00100793          	li	a5,1
   13250:	00c797b3          	sll	a5,a5,a2
   13254:	00a7e7b3          	or	a5,a5,a0
   13258:	00f82223          	sw	a5,4(a6)
   1325c:	eddff06f          	j	13138 <_free_r+0x184>
   13260:	15400613          	li	a2,340
   13264:	00d66c63          	bltu	a2,a3,1327c <_free_r+0x2c8>
   13268:	00f7d693          	srli	a3,a5,0xf
   1326c:	07868593          	addi	a1,a3,120
   13270:	07768613          	addi	a2,a3,119
   13274:	00359593          	slli	a1,a1,0x3
   13278:	e99ff06f          	j	13110 <_free_r+0x15c>
   1327c:	55400613          	li	a2,1364
   13280:	00d66c63          	bltu	a2,a3,13298 <_free_r+0x2e4>
   13284:	0127d693          	srli	a3,a5,0x12
   13288:	07d68593          	addi	a1,a3,125
   1328c:	07c68613          	addi	a2,a3,124
   13290:	00359593          	slli	a1,a1,0x3
   13294:	e7dff06f          	j	13110 <_free_r+0x15c>
   13298:	3f800593          	li	a1,1016
   1329c:	07e00613          	li	a2,126
   132a0:	e71ff06f          	j	13110 <_free_r+0x15c>
   132a4:	0017e693          	ori	a3,a5,1
   132a8:	00d72223          	sw	a3,4(a4)
   132ac:	00f62023          	sw	a5,0(a2)
   132b0:	dd9ff06f          	j	13088 <_free_r+0xd4>

000132b4 <_lseek_r>:
   132b4:	ff010113          	addi	sp,sp,-16
   132b8:	00058713          	mv	a4,a1
   132bc:	00812423          	sw	s0,8(sp)
   132c0:	00060593          	mv	a1,a2
   132c4:	00050413          	mv	s0,a0
   132c8:	00068613          	mv	a2,a3
   132cc:	00070513          	mv	a0,a4
   132d0:	0401a823          	sw	zero,80(gp) # 17bb8 <errno>
   132d4:	00112623          	sw	ra,12(sp)
   132d8:	66c000ef          	jal	ra,13944 <_lseek>
   132dc:	fff00793          	li	a5,-1
   132e0:	00f50a63          	beq	a0,a5,132f4 <_lseek_r+0x40>
   132e4:	00c12083          	lw	ra,12(sp)
   132e8:	00812403          	lw	s0,8(sp)
   132ec:	01010113          	addi	sp,sp,16
   132f0:	00008067          	ret
   132f4:	0501a783          	lw	a5,80(gp) # 17bb8 <errno>
   132f8:	fe0786e3          	beqz	a5,132e4 <_lseek_r+0x30>
   132fc:	00c12083          	lw	ra,12(sp)
   13300:	00f42023          	sw	a5,0(s0)
   13304:	00812403          	lw	s0,8(sp)
   13308:	01010113          	addi	sp,sp,16
   1330c:	00008067          	ret

00013310 <__smakebuf_r>:
   13310:	00c5d783          	lhu	a5,12(a1)
   13314:	f8010113          	addi	sp,sp,-128
   13318:	06812c23          	sw	s0,120(sp)
   1331c:	06112e23          	sw	ra,124(sp)
   13320:	06912a23          	sw	s1,116(sp)
   13324:	07212823          	sw	s2,112(sp)
   13328:	07312623          	sw	s3,108(sp)
   1332c:	07412423          	sw	s4,104(sp)
   13330:	0027f713          	andi	a4,a5,2
   13334:	00058413          	mv	s0,a1
   13338:	02070c63          	beqz	a4,13370 <__smakebuf_r+0x60>
   1333c:	04358793          	addi	a5,a1,67
   13340:	00f5a023          	sw	a5,0(a1)
   13344:	00f5a823          	sw	a5,16(a1)
   13348:	00100793          	li	a5,1
   1334c:	00f5aa23          	sw	a5,20(a1)
   13350:	07c12083          	lw	ra,124(sp)
   13354:	07812403          	lw	s0,120(sp)
   13358:	07412483          	lw	s1,116(sp)
   1335c:	07012903          	lw	s2,112(sp)
   13360:	06c12983          	lw	s3,108(sp)
   13364:	06812a03          	lw	s4,104(sp)
   13368:	08010113          	addi	sp,sp,128
   1336c:	00008067          	ret
   13370:	00e59583          	lh	a1,14(a1)
   13374:	00050493          	mv	s1,a0
   13378:	0805cc63          	bltz	a1,13410 <__smakebuf_r+0x100>
   1337c:	00810613          	addi	a2,sp,8
   13380:	408000ef          	jal	ra,13788 <_fstat_r>
   13384:	08054463          	bltz	a0,1340c <__smakebuf_r+0xfc>
   13388:	00c12783          	lw	a5,12(sp)
   1338c:	0000f937          	lui	s2,0xf
   13390:	00001a37          	lui	s4,0x1
   13394:	00f97933          	and	s2,s2,a5
   13398:	ffffe7b7          	lui	a5,0xffffe
   1339c:	00f90933          	add	s2,s2,a5
   133a0:	00193913          	seqz	s2,s2
   133a4:	40000993          	li	s3,1024
   133a8:	800a0a13          	addi	s4,s4,-2048 # 800 <main-0xf874>
   133ac:	00098593          	mv	a1,s3
   133b0:	00048513          	mv	a0,s1
   133b4:	a08fe0ef          	jal	ra,115bc <_malloc_r>
   133b8:	00c41783          	lh	a5,12(s0)
   133bc:	06050e63          	beqz	a0,13438 <__smakebuf_r+0x128>
   133c0:	ffffe717          	auipc	a4,0xffffe
   133c4:	81070713          	addi	a4,a4,-2032 # 10bd0 <_cleanup_r>
   133c8:	02e4ae23          	sw	a4,60(s1)
   133cc:	0807e793          	ori	a5,a5,128
   133d0:	00f41623          	sh	a5,12(s0)
   133d4:	00a42023          	sw	a0,0(s0)
   133d8:	00a42823          	sw	a0,16(s0)
   133dc:	01342a23          	sw	s3,20(s0)
   133e0:	08091863          	bnez	s2,13470 <__smakebuf_r+0x160>
   133e4:	0147e7b3          	or	a5,a5,s4
   133e8:	07c12083          	lw	ra,124(sp)
   133ec:	00f41623          	sh	a5,12(s0)
   133f0:	07812403          	lw	s0,120(sp)
   133f4:	07412483          	lw	s1,116(sp)
   133f8:	07012903          	lw	s2,112(sp)
   133fc:	06c12983          	lw	s3,108(sp)
   13400:	06812a03          	lw	s4,104(sp)
   13404:	08010113          	addi	sp,sp,128
   13408:	00008067          	ret
   1340c:	00c45783          	lhu	a5,12(s0)
   13410:	0807f793          	andi	a5,a5,128
   13414:	00000913          	li	s2,0
   13418:	04078663          	beqz	a5,13464 <__smakebuf_r+0x154>
   1341c:	04000993          	li	s3,64
   13420:	00098593          	mv	a1,s3
   13424:	00048513          	mv	a0,s1
   13428:	994fe0ef          	jal	ra,115bc <_malloc_r>
   1342c:	00c41783          	lh	a5,12(s0)
   13430:	00000a13          	li	s4,0
   13434:	f80516e3          	bnez	a0,133c0 <__smakebuf_r+0xb0>
   13438:	2007f713          	andi	a4,a5,512
   1343c:	f0071ae3          	bnez	a4,13350 <__smakebuf_r+0x40>
   13440:	ffc7f793          	andi	a5,a5,-4
   13444:	0027e793          	ori	a5,a5,2
   13448:	04340713          	addi	a4,s0,67
   1344c:	00f41623          	sh	a5,12(s0)
   13450:	00100793          	li	a5,1
   13454:	00e42023          	sw	a4,0(s0)
   13458:	00e42823          	sw	a4,16(s0)
   1345c:	00f42a23          	sw	a5,20(s0)
   13460:	ef1ff06f          	j	13350 <__smakebuf_r+0x40>
   13464:	40000993          	li	s3,1024
   13468:	00000a13          	li	s4,0
   1346c:	f41ff06f          	j	133ac <__smakebuf_r+0x9c>
   13470:	00e41583          	lh	a1,14(s0)
   13474:	00048513          	mv	a0,s1
   13478:	368000ef          	jal	ra,137e0 <_isatty_r>
   1347c:	00051663          	bnez	a0,13488 <__smakebuf_r+0x178>
   13480:	00c41783          	lh	a5,12(s0)
   13484:	f61ff06f          	j	133e4 <__smakebuf_r+0xd4>
   13488:	00c45783          	lhu	a5,12(s0)
   1348c:	ffc7f793          	andi	a5,a5,-4
   13490:	0017e793          	ori	a5,a5,1
   13494:	01079793          	slli	a5,a5,0x10
   13498:	4107d793          	srai	a5,a5,0x10
   1349c:	f49ff06f          	j	133e4 <__smakebuf_r+0xd4>

000134a0 <__swhatbuf_r>:
   134a0:	f9010113          	addi	sp,sp,-112
   134a4:	06812423          	sw	s0,104(sp)
   134a8:	00058413          	mv	s0,a1
   134ac:	00e59583          	lh	a1,14(a1)
   134b0:	06912223          	sw	s1,100(sp)
   134b4:	07212023          	sw	s2,96(sp)
   134b8:	06112623          	sw	ra,108(sp)
   134bc:	00060493          	mv	s1,a2
   134c0:	00068913          	mv	s2,a3
   134c4:	0405ca63          	bltz	a1,13518 <__swhatbuf_r+0x78>
   134c8:	00810613          	addi	a2,sp,8
   134cc:	2bc000ef          	jal	ra,13788 <_fstat_r>
   134d0:	04054463          	bltz	a0,13518 <__swhatbuf_r+0x78>
   134d4:	00c12703          	lw	a4,12(sp)
   134d8:	0000f7b7          	lui	a5,0xf
   134dc:	06c12083          	lw	ra,108(sp)
   134e0:	00e7f7b3          	and	a5,a5,a4
   134e4:	ffffe737          	lui	a4,0xffffe
   134e8:	00e787b3          	add	a5,a5,a4
   134ec:	06812403          	lw	s0,104(sp)
   134f0:	0017b793          	seqz	a5,a5
   134f4:	00f92023          	sw	a5,0(s2) # f000 <main-0x1074>
   134f8:	40000713          	li	a4,1024
   134fc:	00e4a023          	sw	a4,0(s1)
   13500:	00001537          	lui	a0,0x1
   13504:	06412483          	lw	s1,100(sp)
   13508:	06012903          	lw	s2,96(sp)
   1350c:	80050513          	addi	a0,a0,-2048 # 800 <main-0xf874>
   13510:	07010113          	addi	sp,sp,112
   13514:	00008067          	ret
   13518:	00c45783          	lhu	a5,12(s0)
   1351c:	0807f793          	andi	a5,a5,128
   13520:	02078863          	beqz	a5,13550 <__swhatbuf_r+0xb0>
   13524:	06c12083          	lw	ra,108(sp)
   13528:	06812403          	lw	s0,104(sp)
   1352c:	00000793          	li	a5,0
   13530:	00f92023          	sw	a5,0(s2)
   13534:	04000713          	li	a4,64
   13538:	00e4a023          	sw	a4,0(s1)
   1353c:	06012903          	lw	s2,96(sp)
   13540:	06412483          	lw	s1,100(sp)
   13544:	00000513          	li	a0,0
   13548:	07010113          	addi	sp,sp,112
   1354c:	00008067          	ret
   13550:	06c12083          	lw	ra,108(sp)
   13554:	06812403          	lw	s0,104(sp)
   13558:	00000793          	li	a5,0
   1355c:	00f92023          	sw	a5,0(s2)
   13560:	40000713          	li	a4,1024
   13564:	00e4a023          	sw	a4,0(s1)
   13568:	06012903          	lw	s2,96(sp)
   1356c:	06412483          	lw	s1,100(sp)
   13570:	00000513          	li	a0,0
   13574:	07010113          	addi	sp,sp,112
   13578:	00008067          	ret

0001357c <_read_r>:
   1357c:	ff010113          	addi	sp,sp,-16
   13580:	00058713          	mv	a4,a1
   13584:	00812423          	sw	s0,8(sp)
   13588:	00060593          	mv	a1,a2
   1358c:	00050413          	mv	s0,a0
   13590:	00068613          	mv	a2,a3
   13594:	00070513          	mv	a0,a4
   13598:	0401a823          	sw	zero,80(gp) # 17bb8 <errno>
   1359c:	00112623          	sw	ra,12(sp)
   135a0:	3e8000ef          	jal	ra,13988 <_read>
   135a4:	fff00793          	li	a5,-1
   135a8:	00f50a63          	beq	a0,a5,135bc <_read_r+0x40>
   135ac:	00c12083          	lw	ra,12(sp)
   135b0:	00812403          	lw	s0,8(sp)
   135b4:	01010113          	addi	sp,sp,16
   135b8:	00008067          	ret
   135bc:	0501a783          	lw	a5,80(gp) # 17bb8 <errno>
   135c0:	fe0786e3          	beqz	a5,135ac <_read_r+0x30>
   135c4:	00c12083          	lw	ra,12(sp)
   135c8:	00f42023          	sw	a5,0(s0)
   135cc:	00812403          	lw	s0,8(sp)
   135d0:	01010113          	addi	sp,sp,16
   135d4:	00008067          	ret

000135d8 <cleanup_glue>:
   135d8:	fe010113          	addi	sp,sp,-32
   135dc:	01212823          	sw	s2,16(sp)
   135e0:	0005a903          	lw	s2,0(a1)
   135e4:	00812c23          	sw	s0,24(sp)
   135e8:	00912a23          	sw	s1,20(sp)
   135ec:	00112e23          	sw	ra,28(sp)
   135f0:	01312623          	sw	s3,12(sp)
   135f4:	01412423          	sw	s4,8(sp)
   135f8:	00058413          	mv	s0,a1
   135fc:	00050493          	mv	s1,a0
   13600:	04090263          	beqz	s2,13644 <cleanup_glue+0x6c>
   13604:	00092983          	lw	s3,0(s2)
   13608:	02098863          	beqz	s3,13638 <cleanup_glue+0x60>
   1360c:	0009aa03          	lw	s4,0(s3)
   13610:	000a0e63          	beqz	s4,1362c <cleanup_glue+0x54>
   13614:	000a2583          	lw	a1,0(s4)
   13618:	00058463          	beqz	a1,13620 <cleanup_glue+0x48>
   1361c:	fbdff0ef          	jal	ra,135d8 <cleanup_glue>
   13620:	000a0593          	mv	a1,s4
   13624:	00048513          	mv	a0,s1
   13628:	98dff0ef          	jal	ra,12fb4 <_free_r>
   1362c:	00098593          	mv	a1,s3
   13630:	00048513          	mv	a0,s1
   13634:	981ff0ef          	jal	ra,12fb4 <_free_r>
   13638:	00090593          	mv	a1,s2
   1363c:	00048513          	mv	a0,s1
   13640:	975ff0ef          	jal	ra,12fb4 <_free_r>
   13644:	00040593          	mv	a1,s0
   13648:	01812403          	lw	s0,24(sp)
   1364c:	01c12083          	lw	ra,28(sp)
   13650:	01012903          	lw	s2,16(sp)
   13654:	00c12983          	lw	s3,12(sp)
   13658:	00812a03          	lw	s4,8(sp)
   1365c:	00048513          	mv	a0,s1
   13660:	01412483          	lw	s1,20(sp)
   13664:	02010113          	addi	sp,sp,32
   13668:	94dff06f          	j	12fb4 <_free_r>

0001366c <_reclaim_reent>:
   1366c:	0381a783          	lw	a5,56(gp) # 17ba0 <_impure_ptr>
   13670:	10a78a63          	beq	a5,a0,13784 <_reclaim_reent+0x118>
   13674:	04c52583          	lw	a1,76(a0)
   13678:	fe010113          	addi	sp,sp,-32
   1367c:	00912a23          	sw	s1,20(sp)
   13680:	00112e23          	sw	ra,28(sp)
   13684:	00812c23          	sw	s0,24(sp)
   13688:	01212823          	sw	s2,16(sp)
   1368c:	01312623          	sw	s3,12(sp)
   13690:	00050493          	mv	s1,a0
   13694:	04058063          	beqz	a1,136d4 <_reclaim_reent+0x68>
   13698:	00000913          	li	s2,0
   1369c:	08000993          	li	s3,128
   136a0:	012587b3          	add	a5,a1,s2
   136a4:	0007a403          	lw	s0,0(a5) # f000 <main-0x1074>
   136a8:	00040e63          	beqz	s0,136c4 <_reclaim_reent+0x58>
   136ac:	00040593          	mv	a1,s0
   136b0:	00042403          	lw	s0,0(s0)
   136b4:	00048513          	mv	a0,s1
   136b8:	8fdff0ef          	jal	ra,12fb4 <_free_r>
   136bc:	fe0418e3          	bnez	s0,136ac <_reclaim_reent+0x40>
   136c0:	04c4a583          	lw	a1,76(s1)
   136c4:	00490913          	addi	s2,s2,4
   136c8:	fd391ce3          	bne	s2,s3,136a0 <_reclaim_reent+0x34>
   136cc:	00048513          	mv	a0,s1
   136d0:	8e5ff0ef          	jal	ra,12fb4 <_free_r>
   136d4:	0404a583          	lw	a1,64(s1)
   136d8:	00058663          	beqz	a1,136e4 <_reclaim_reent+0x78>
   136dc:	00048513          	mv	a0,s1
   136e0:	8d5ff0ef          	jal	ra,12fb4 <_free_r>
   136e4:	1484a403          	lw	s0,328(s1)
   136e8:	02040063          	beqz	s0,13708 <_reclaim_reent+0x9c>
   136ec:	14c48913          	addi	s2,s1,332
   136f0:	01240c63          	beq	s0,s2,13708 <_reclaim_reent+0x9c>
   136f4:	00040593          	mv	a1,s0
   136f8:	00042403          	lw	s0,0(s0)
   136fc:	00048513          	mv	a0,s1
   13700:	8b5ff0ef          	jal	ra,12fb4 <_free_r>
   13704:	fe8918e3          	bne	s2,s0,136f4 <_reclaim_reent+0x88>
   13708:	0544a583          	lw	a1,84(s1)
   1370c:	00058663          	beqz	a1,13718 <_reclaim_reent+0xac>
   13710:	00048513          	mv	a0,s1
   13714:	8a1ff0ef          	jal	ra,12fb4 <_free_r>
   13718:	0384a783          	lw	a5,56(s1)
   1371c:	04078663          	beqz	a5,13768 <_reclaim_reent+0xfc>
   13720:	03c4a783          	lw	a5,60(s1)
   13724:	00048513          	mv	a0,s1
   13728:	000780e7          	jalr	a5
   1372c:	2e04a403          	lw	s0,736(s1)
   13730:	02040c63          	beqz	s0,13768 <_reclaim_reent+0xfc>
   13734:	00042583          	lw	a1,0(s0)
   13738:	00058663          	beqz	a1,13744 <_reclaim_reent+0xd8>
   1373c:	00048513          	mv	a0,s1
   13740:	e99ff0ef          	jal	ra,135d8 <cleanup_glue>
   13744:	00040593          	mv	a1,s0
   13748:	01812403          	lw	s0,24(sp)
   1374c:	01c12083          	lw	ra,28(sp)
   13750:	01012903          	lw	s2,16(sp)
   13754:	00c12983          	lw	s3,12(sp)
   13758:	00048513          	mv	a0,s1
   1375c:	01412483          	lw	s1,20(sp)
   13760:	02010113          	addi	sp,sp,32
   13764:	851ff06f          	j	12fb4 <_free_r>
   13768:	01c12083          	lw	ra,28(sp)
   1376c:	01812403          	lw	s0,24(sp)
   13770:	01412483          	lw	s1,20(sp)
   13774:	01012903          	lw	s2,16(sp)
   13778:	00c12983          	lw	s3,12(sp)
   1377c:	02010113          	addi	sp,sp,32
   13780:	00008067          	ret
   13784:	00008067          	ret

00013788 <_fstat_r>:
   13788:	ff010113          	addi	sp,sp,-16
   1378c:	00058713          	mv	a4,a1
   13790:	00812423          	sw	s0,8(sp)
   13794:	00060593          	mv	a1,a2
   13798:	00050413          	mv	s0,a0
   1379c:	00070513          	mv	a0,a4
   137a0:	0401a823          	sw	zero,80(gp) # 17bb8 <errno>
   137a4:	00112623          	sw	ra,12(sp)
   137a8:	0fc000ef          	jal	ra,138a4 <_fstat>
   137ac:	fff00793          	li	a5,-1
   137b0:	00f50a63          	beq	a0,a5,137c4 <_fstat_r+0x3c>
   137b4:	00c12083          	lw	ra,12(sp)
   137b8:	00812403          	lw	s0,8(sp)
   137bc:	01010113          	addi	sp,sp,16
   137c0:	00008067          	ret
   137c4:	0501a783          	lw	a5,80(gp) # 17bb8 <errno>
   137c8:	fe0786e3          	beqz	a5,137b4 <_fstat_r+0x2c>
   137cc:	00c12083          	lw	ra,12(sp)
   137d0:	00f42023          	sw	a5,0(s0)
   137d4:	00812403          	lw	s0,8(sp)
   137d8:	01010113          	addi	sp,sp,16
   137dc:	00008067          	ret

000137e0 <_isatty_r>:
   137e0:	ff010113          	addi	sp,sp,-16
   137e4:	00812423          	sw	s0,8(sp)
   137e8:	00050413          	mv	s0,a0
   137ec:	00058513          	mv	a0,a1
   137f0:	0401a823          	sw	zero,80(gp) # 17bb8 <errno>
   137f4:	00112623          	sw	ra,12(sp)
   137f8:	10c000ef          	jal	ra,13904 <_isatty>
   137fc:	fff00793          	li	a5,-1
   13800:	00f50a63          	beq	a0,a5,13814 <_isatty_r+0x34>
   13804:	00c12083          	lw	ra,12(sp)
   13808:	00812403          	lw	s0,8(sp)
   1380c:	01010113          	addi	sp,sp,16
   13810:	00008067          	ret
   13814:	0501a783          	lw	a5,80(gp) # 17bb8 <errno>
   13818:	fe0786e3          	beqz	a5,13804 <_isatty_r+0x24>
   1381c:	00c12083          	lw	ra,12(sp)
   13820:	00f42023          	sw	a5,0(s0)
   13824:	00812403          	lw	s0,8(sp)
   13828:	01010113          	addi	sp,sp,16
   1382c:	00008067          	ret

00013830 <_close>:
   13830:	ff010113          	addi	sp,sp,-16
   13834:	00112623          	sw	ra,12(sp)
   13838:	00812423          	sw	s0,8(sp)
   1383c:	03900893          	li	a7,57
   13840:	00000073          	ecall
   13844:	00050413          	mv	s0,a0
   13848:	00054c63          	bltz	a0,13860 <_close+0x30>
   1384c:	00c12083          	lw	ra,12(sp)
   13850:	00040513          	mv	a0,s0
   13854:	00812403          	lw	s0,8(sp)
   13858:	01010113          	addi	sp,sp,16
   1385c:	00008067          	ret
   13860:	40800433          	neg	s0,s0
   13864:	2cc000ef          	jal	ra,13b30 <__errno>
   13868:	00852023          	sw	s0,0(a0)
   1386c:	fff00413          	li	s0,-1
   13870:	fddff06f          	j	1384c <_close+0x1c>

00013874 <_exit>:
   13874:	05d00893          	li	a7,93
   13878:	00000073          	ecall
   1387c:	00054463          	bltz	a0,13884 <_exit+0x10>
   13880:	0000006f          	j	13880 <_exit+0xc>
   13884:	ff010113          	addi	sp,sp,-16
   13888:	00812423          	sw	s0,8(sp)
   1388c:	00050413          	mv	s0,a0
   13890:	00112623          	sw	ra,12(sp)
   13894:	40800433          	neg	s0,s0
   13898:	298000ef          	jal	ra,13b30 <__errno>
   1389c:	00852023          	sw	s0,0(a0)
   138a0:	0000006f          	j	138a0 <_exit+0x2c>

000138a4 <_fstat>:
   138a4:	f7010113          	addi	sp,sp,-144
   138a8:	08912223          	sw	s1,132(sp)
   138ac:	08112623          	sw	ra,140(sp)
   138b0:	00058493          	mv	s1,a1
   138b4:	08812423          	sw	s0,136(sp)
   138b8:	05000893          	li	a7,80
   138bc:	00010593          	mv	a1,sp
   138c0:	00000073          	ecall
   138c4:	00050413          	mv	s0,a0
   138c8:	02054463          	bltz	a0,138f0 <_fstat+0x4c>
   138cc:	00048513          	mv	a0,s1
   138d0:	00010593          	mv	a1,sp
   138d4:	1b8000ef          	jal	ra,13a8c <_conv_stat>
   138d8:	08c12083          	lw	ra,140(sp)
   138dc:	00040513          	mv	a0,s0
   138e0:	08812403          	lw	s0,136(sp)
   138e4:	08412483          	lw	s1,132(sp)
   138e8:	09010113          	addi	sp,sp,144
   138ec:	00008067          	ret
   138f0:	40800433          	neg	s0,s0
   138f4:	23c000ef          	jal	ra,13b30 <__errno>
   138f8:	00852023          	sw	s0,0(a0)
   138fc:	fff00413          	li	s0,-1
   13900:	fcdff06f          	j	138cc <_fstat+0x28>

00013904 <_isatty>:
   13904:	f9010113          	addi	sp,sp,-112
   13908:	00810593          	addi	a1,sp,8
   1390c:	06112623          	sw	ra,108(sp)
   13910:	f95ff0ef          	jal	ra,138a4 <_fstat>
   13914:	fff00793          	li	a5,-1
   13918:	00f50e63          	beq	a0,a5,13934 <_isatty+0x30>
   1391c:	00c12503          	lw	a0,12(sp)
   13920:	06c12083          	lw	ra,108(sp)
   13924:	00d55513          	srli	a0,a0,0xd
   13928:	00157513          	andi	a0,a0,1
   1392c:	07010113          	addi	sp,sp,112
   13930:	00008067          	ret
   13934:	06c12083          	lw	ra,108(sp)
   13938:	00000513          	li	a0,0
   1393c:	07010113          	addi	sp,sp,112
   13940:	00008067          	ret

00013944 <_lseek>:
   13944:	ff010113          	addi	sp,sp,-16
   13948:	00112623          	sw	ra,12(sp)
   1394c:	00812423          	sw	s0,8(sp)
   13950:	03e00893          	li	a7,62
   13954:	00000073          	ecall
   13958:	00050413          	mv	s0,a0
   1395c:	00054c63          	bltz	a0,13974 <_lseek+0x30>
   13960:	00c12083          	lw	ra,12(sp)
   13964:	00040513          	mv	a0,s0
   13968:	00812403          	lw	s0,8(sp)
   1396c:	01010113          	addi	sp,sp,16
   13970:	00008067          	ret
   13974:	40800433          	neg	s0,s0
   13978:	1b8000ef          	jal	ra,13b30 <__errno>
   1397c:	00852023          	sw	s0,0(a0)
   13980:	fff00413          	li	s0,-1
   13984:	fddff06f          	j	13960 <_lseek+0x1c>

00013988 <_read>:
   13988:	ff010113          	addi	sp,sp,-16
   1398c:	00112623          	sw	ra,12(sp)
   13990:	00812423          	sw	s0,8(sp)
   13994:	03f00893          	li	a7,63
   13998:	00000073          	ecall
   1399c:	00050413          	mv	s0,a0
   139a0:	00054c63          	bltz	a0,139b8 <_read+0x30>
   139a4:	00c12083          	lw	ra,12(sp)
   139a8:	00040513          	mv	a0,s0
   139ac:	00812403          	lw	s0,8(sp)
   139b0:	01010113          	addi	sp,sp,16
   139b4:	00008067          	ret
   139b8:	40800433          	neg	s0,s0
   139bc:	174000ef          	jal	ra,13b30 <__errno>
   139c0:	00852023          	sw	s0,0(a0)
   139c4:	fff00413          	li	s0,-1
   139c8:	fddff06f          	j	139a4 <_read+0x1c>

000139cc <_sbrk>:
   139cc:	05418693          	addi	a3,gp,84 # 17bbc <heap_end.0>
   139d0:	0006a703          	lw	a4,0(a3)
   139d4:	ff010113          	addi	sp,sp,-16
   139d8:	00112623          	sw	ra,12(sp)
   139dc:	00050793          	mv	a5,a0
   139e0:	02071063          	bnez	a4,13a00 <_sbrk+0x34>
   139e4:	0d600893          	li	a7,214
   139e8:	00000513          	li	a0,0
   139ec:	00000073          	ecall
   139f0:	fff00613          	li	a2,-1
   139f4:	00050713          	mv	a4,a0
   139f8:	02c50a63          	beq	a0,a2,13a2c <_sbrk+0x60>
   139fc:	00a6a023          	sw	a0,0(a3)
   13a00:	0d600893          	li	a7,214
   13a04:	00e78533          	add	a0,a5,a4
   13a08:	00000073          	ecall
   13a0c:	0006a703          	lw	a4,0(a3)
   13a10:	00e787b3          	add	a5,a5,a4
   13a14:	00f51c63          	bne	a0,a5,13a2c <_sbrk+0x60>
   13a18:	00c12083          	lw	ra,12(sp)
   13a1c:	00a6a023          	sw	a0,0(a3)
   13a20:	00070513          	mv	a0,a4
   13a24:	01010113          	addi	sp,sp,16
   13a28:	00008067          	ret
   13a2c:	104000ef          	jal	ra,13b30 <__errno>
   13a30:	00c12083          	lw	ra,12(sp)
   13a34:	00c00793          	li	a5,12
   13a38:	00f52023          	sw	a5,0(a0)
   13a3c:	fff00513          	li	a0,-1
   13a40:	01010113          	addi	sp,sp,16
   13a44:	00008067          	ret

00013a48 <_write>:
   13a48:	ff010113          	addi	sp,sp,-16
   13a4c:	00112623          	sw	ra,12(sp)
   13a50:	00812423          	sw	s0,8(sp)
   13a54:	04000893          	li	a7,64
   13a58:	00000073          	ecall
   13a5c:	00050413          	mv	s0,a0
   13a60:	00054c63          	bltz	a0,13a78 <_write+0x30>
   13a64:	00c12083          	lw	ra,12(sp)
   13a68:	00040513          	mv	a0,s0
   13a6c:	00812403          	lw	s0,8(sp)
   13a70:	01010113          	addi	sp,sp,16
   13a74:	00008067          	ret
   13a78:	40800433          	neg	s0,s0
   13a7c:	0b4000ef          	jal	ra,13b30 <__errno>
   13a80:	00852023          	sw	s0,0(a0)
   13a84:	fff00413          	li	s0,-1
   13a88:	fddff06f          	j	13a64 <_write+0x1c>

00013a8c <_conv_stat>:
   13a8c:	ff010113          	addi	sp,sp,-16
   13a90:	0145a383          	lw	t2,20(a1)
   13a94:	0185a283          	lw	t0,24(a1)
   13a98:	01c5af83          	lw	t6,28(a1)
   13a9c:	0205af03          	lw	t5,32(a1)
   13aa0:	0305ae83          	lw	t4,48(a1)
   13aa4:	0405ae03          	lw	t3,64(a1)
   13aa8:	0385a303          	lw	t1,56(a1)
   13aac:	0485a803          	lw	a6,72(a1)
   13ab0:	04c5a883          	lw	a7,76(a1)
   13ab4:	0585a603          	lw	a2,88(a1)
   13ab8:	00812623          	sw	s0,12(sp)
   13abc:	00912423          	sw	s1,8(sp)
   13ac0:	0105a403          	lw	s0,16(a1)
   13ac4:	0085a483          	lw	s1,8(a1)
   13ac8:	01212223          	sw	s2,4(sp)
   13acc:	0005a903          	lw	s2,0(a1)
   13ad0:	05c5a683          	lw	a3,92(a1)
   13ad4:	0685a703          	lw	a4,104(a1)
   13ad8:	06c5a783          	lw	a5,108(a1)
   13adc:	01251023          	sh	s2,0(a0)
   13ae0:	00951123          	sh	s1,2(a0)
   13ae4:	00852223          	sw	s0,4(a0)
   13ae8:	00751423          	sh	t2,8(a0)
   13aec:	00551523          	sh	t0,10(a0)
   13af0:	01f51623          	sh	t6,12(a0)
   13af4:	01e51723          	sh	t5,14(a0)
   13af8:	01d52823          	sw	t4,16(a0)
   13afc:	05c52623          	sw	t3,76(a0)
   13b00:	04652423          	sw	t1,72(a0)
   13b04:	01052c23          	sw	a6,24(a0)
   13b08:	01152e23          	sw	a7,28(a0)
   13b0c:	02c52423          	sw	a2,40(a0)
   13b10:	02d52623          	sw	a3,44(a0)
   13b14:	00c12403          	lw	s0,12(sp)
   13b18:	02e52c23          	sw	a4,56(a0)
   13b1c:	02f52e23          	sw	a5,60(a0)
   13b20:	00812483          	lw	s1,8(sp)
   13b24:	00412903          	lw	s2,4(sp)
   13b28:	01010113          	addi	sp,sp,16
   13b2c:	00008067          	ret

00013b30 <__errno>:
   13b30:	0381a503          	lw	a0,56(gp) # 17ba0 <_impure_ptr>
   13b34:	00008067          	ret

Disassembly of section .rodata:

00013b38 <iGMb-0x18>:
   13b38:	00006b6f          	jal	s6,19b38 <__BSS_END__+0x1f34>
   13b3c:	6166                	flw	ft2,88(sp)
   13b3e:	6c69                	lui	s8,0x1a
   13b40:	6465                	lui	s0,0x19
   13b42:	7420                	flw	fs0,104(s0)
   13b44:	6576206f          	j	7699a <__BSS_END__+0x5ed96>
   13b48:	6972                	flw	fs2,28(sp)
   13b4a:	7966                	flw	fs2,120(sp)
   13b4c:	0000                	unimp
	...

00013b50 <iGMb>:
   13b50:	11310ffb          	0x11310ffb
   13b54:	0439                	addi	s0,s0,14
   13b56:	04cd                	addi	s1,s1,19
   13b58:	09e2                	slli	s3,s3,0x18
   13b5a:	177e                	slli	a4,a4,0x3f
   13b5c:	14d11f0b          	0x14d11f0b
   13b60:	128f0a13          	addi	s4,t5,296
   13b64:	1940                	addi	s0,sp,180
   13b66:	1b6f2db7          	lui	s11,0x1b6f2
   13b6a:	0afc                	addi	a5,sp,348
   13b6c:	1702                	slli	a4,a4,0x20
   13b6e:	29ca                	fld	fs3,144(sp)
   13b70:	0c25                	addi	s8,s8,9
   13b72:	084d                	addi	a6,a6,19
   13b74:	07a8                	addi	a0,sp,968
   13b76:	2aad                	jal	13cf0 <iGMb+0x1a0>
   13b78:	2969                	jal	14012 <iGMb+0x4c2>
   13b7a:	28a4                	fld	fs1,80(s1)
   13b7c:	105d                	c.nop	-9
   13b7e:	16d70753          	fmul.q	fa4,fa4,fa3,rne
   13b82:	2162                	fld	ft2,24(sp)
   13b84:	14461207          	0x14461207
   13b88:	2c3c                	fld	fa5,88(s0)
   13b8a:	2952                	fld	fs2,272(sp)
   13b8c:	16fa                	slli	a3,a3,0x3e
   13b8e:	20e12b93          	slti	s7,sp,526
   13b92:	29672ff3          	csrrs	t6,0x296,a4
   13b96:	1d16                	slli	s10,s10,0x25
   13b98:	0df11657          	0xdf11657
   13b9c:	175d                	addi	a4,a4,-9
   13b9e:	277c                	fld	fa5,200(a4)
   13ba0:	114a                	slli	sp,sp,0x32
   13ba2:	2072                	fld	ft0,280(sp)
   13ba4:	12472a03          	lw	s4,292(a4) # ffffe124 <__BSS_END__+0xfffe6520>
   13ba8:	2b2c                	fld	fa1,80(a4)
   13baa:	0602                	c.slli64	a2
   13bac:	2e51                	jal	13f40 <iGMb+0x3f0>
   13bae:	0064                	addi	s1,sp,12
   13bb0:	19e12037          	lui	zero,0x19e12
   13bb4:	25fd                	jal	142a2 <iGMb+0x752>
   13bb6:	1419                	addi	s0,s0,-26
   13bb8:	0d54                	addi	a3,sp,660
   13bba:	1eb2                	slli	t4,t4,0x2c
   13bbc:	24f416c7          	0x24f416c7
   13bc0:	1461                	addi	s0,s0,-8
   13bc2:	29f4                	fld	fa3,208(a1)
   13bc4:	1eca                	slli	t4,t4,0x32
   13bc6:	1d52                	slli	s10,s10,0x34
   13bc8:	2f8c                	fld	fa1,24(a5)
   13bca:	2c1c                	fld	fa5,24(s0)
   13bcc:	17a1                	addi	a5,a5,-24
   13bce:	000d004f          	fnmadd.s	ft0,fs10,ft0,ft0,rne
   13bd2:	1b1a                	slli	s6,s6,0x26
   13bd4:	22b6                	fld	ft5,328(sp)
   13bd6:	154d                	addi	a0,a0,-13
   13bd8:	11ea                	slli	gp,gp,0x3a
   13bda:	0b572cbf 26731244 	0x267312440b572cbf
   13be2:	1dc5                	addi	s11,s11,-15
   13be4:	2276                	fld	ft4,344(sp)
   13be6:	2395                	jal	1414a <iGMb+0x5fa>
   13be8:	213b0823          	sb	s3,528(s6)
   13bec:	21ed                	jal	140d6 <iGMb+0x586>
   13bee:	0c26                	slli	s8,s8,0x9
   13bf0:	0cc51b67          	0xcc51b67
   13bf4:	18fd0557          	0x18fd0557
   13bf8:	20f32813          	slti	a6,t1,527
   13bfc:	291f 2d27 2b56      	0x2b562d27291f
   13c02:	071008a3          	sb	a7,113(zero) # 71 <main-0x10003>
   13c06:	00301c97          	auipc	s9,0x301
   13c0a:	0a00254b          	fnmsub.d	fa0,ft0,ft0,ft1,rdn
   13c0e:	04cc                	addi	a1,sp,580
   13c10:	24de                	fld	fs1,464(sp)
   13c12:	2e182a23          	sw	ra,756(a6)
   13c16:	071c                	addi	a5,sp,896
   13c18:	2c8e                	fld	fs9,192(sp)
   13c1a:	2306                	fld	ft6,64(sp)
   13c1c:	0bc4180f          	0xbc4180f
   13c20:	17dd                	addi	a5,a5,-9
   13c22:	0aec                	addi	a1,sp,348
   13c24:	0674089b          	0x674089b
   13c28:	1b5c02c7          	fmsub.d	ft5,fs8,fs5,ft3,rne
   13c2c:	041d                	addi	s0,s0,7
   13c2e:	230d                	jal	14150 <iGMb+0x600>
   13c30:	147c                	addi	a5,sp,556
   13c32:	05ed                	addi	a1,a1,27
   13c34:	246a                	fld	fs0,152(sp)
   13c36:	2c05                	jal	13e66 <iGMb+0x316>
   13c38:	0384                	addi	s1,sp,448
   13c3a:	0f30                	addi	a2,sp,920
   13c3c:	2b7d                	jal	141fa <iGMb+0x6aa>
   13c3e:	29f0                	fld	fa2,208(a1)
   13c40:	1355                	addi	t1,t1,-11
   13c42:	1dc0                	addi	s0,sp,756
   13c44:	26f6                	fld	fa3,344(sp)
   13c46:	128a                	slli	t0,t0,0x22
   13c48:	281e                	fld	fa6,448(sp)
   13c4a:	007e                	c.slli	zero,0x1f
   13c4c:	0b69                	addi	s6,s6,26
   13c4e:	1a40                	addi	s0,sp,308
   13c50:	198f19eb          	0x198f19eb
   13c54:	062e                	slli	a2,a2,0xb
   13c56:	1304                	addi	s1,sp,416
   13c58:	002a                	c.slli	zero,0xa
   13c5a:	02a1                	addi	t0,t0,8
   13c5c:	08c0                	addi	s0,sp,84
   13c5e:	05101c33          	0x5101c33
   13c62:	2ed5                	jal	14056 <iGMb+0x506>
   13c64:	21821dfb          	0x21821dfb
   13c68:	2ead                	jal	13fe2 <iGMb+0x492>
   13c6a:	03dd                	addi	t2,t2,23
   13c6c:	292d                	jal	140a6 <iGMb+0x556>
   13c6e:	1bad1e07          	0x1bad1e07
   13c72:	03ec2127          	fsw	ft10,34(s8) # 1a022 <__BSS_END__+0x241e>
   13c76:	27fc                	fld	fa5,200(a5)
   13c78:	125f 00a3 23b7      	0x23b700a3125f
   13c7e:	11f5                	addi	gp,gp,-3
   13c80:	191f 2f14 0baf      	0xbaf2f14191f
   13c86:	2ea2                	fld	ft9,8(sp)
   13c88:	0d221227          	0xd221227
   13c8c:	080c                	addi	a1,sp,16
   13c8e:	2c5d                	jal	13f44 <iGMb+0x3f4>
   13c90:	1a082eeb          	0x1a082eeb
   13c94:	1c391617          	auipc	a2,0x1c391
   13c98:	171a                	slli	a4,a4,0x26
   13c9a:	0ffc246f          	jal	s0,d6598 <__BSS_END__+0xbe994>
   13c9e:	16f8                	addi	a4,sp,876
   13ca0:	1b14                	addi	a3,sp,432
   13ca2:	0d4a                	slli	s10,s10,0x12
   13ca4:	140d                	addi	s0,s0,-29
   13ca6:	24b2                	fld	fs1,264(sp)
   13ca8:	2bdd                	jal	1429e <iGMb+0x74e>
   13caa:	1484                	addi	s1,sp,608
   13cac:	2330                	fld	fa2,64(a4)
   13cae:	0614                	addi	a3,sp,768
   13cb0:	1afc                	addi	a5,sp,380
   13cb2:	12a5                	addi	t0,t0,-23
   13cb4:	0f0d                	addi	t5,t5,3
   13cb6:	224c                	fld	fa1,128(a2)
   13cb8:	2855                	jal	13d6c <iGMb+0x21c>
   13cba:	1e39                	addi	t3,t3,-18
   13cbc:	06de                	slli	a3,a3,0x17
   13cbe:	2c6f1bbf 219a2ff1 	0x219a2ff12c6f1bbf
   13cc6:	19880cab          	0x19880cab
   13cca:	1da6                	slli	s11,s11,0x29
   13ccc:	2d20218f          	0x2d20218f
   13cd0:	17d5                	addi	a5,a5,-11
   13cd2:	0cb5                	addi	s9,s9,13
   13cd4:	26f1                	jal	140a0 <iGMb+0x550>
   13cd6:	25a8                	fld	fa0,72(a1)
   13cd8:	119a                	slli	gp,gp,0x26
   13cda:	0e98                	addi	a4,sp,848
   13cdc:	1aad                	addi	s5,s5,-21
   13cde:	2a46                	fld	fs4,80(sp)
   13ce0:	23aa                	fld	ft7,136(sp)
   13ce2:	26dc                	fld	fa5,136(a3)
   13ce4:	0dee                	slli	s11,s11,0x1b
   13ce6:	0855                	addi	a6,a6,21
   13ce8:	0f3d                	addi	t5,t5,15
   13cea:	1796                	slli	a5,a5,0x25
   13cec:	1ca5                	addi	s9,s9,-23
   13cee:	19d1                	addi	s3,s3,-12
   13cf0:	0d8c                	addi	a1,sp,720
   13cf2:	02711233          	mulh	tp,sp,t2
   13cf6:	0a8c                	addi	a1,sp,336
   13cf8:	1e3a                	slli	t3,t3,0x2e
   13cfa:	0bf40d73          	0xbf40d73
   13cfe:	0d3c                	addi	a5,sp,664
   13d00:	0dc6                	slli	s11,s11,0x11
   13d02:	1142                	slli	sp,sp,0x30
   13d04:	18582e87          	flw	ft9,389(a6)
   13d08:	06c2                	slli	a3,a3,0x10
   13d0a:	09fe                	slli	s3,s3,0x1f
   13d0c:	2864                	fld	fs1,208(s0)
   13d0e:	14e0                	addi	s0,sp,620
   13d10:	14a6                	slli	s1,s1,0x29
   13d12:	088e                	slli	a7,a7,0x3
   13d14:	2d2a                	fld	fs10,136(sp)
   13d16:	09b21837          	lui	a6,0x9b21
   13d1a:	2234                	fld	fa3,64(a2)
   13d1c:	1005150b          	0x1005150b
   13d20:	1201                	addi	tp,tp,-32
   13d22:	219d                	jal	14188 <iGMb+0x638>
   13d24:	2022                	fld	ft0,8(sp)
   13d26:	0090                	addi	a2,sp,64
   13d28:	1618                	addi	a4,sp,800
   13d2a:	2200                	fld	fs0,0(a2)
   13d2c:	0a3d                	addi	s4,s4,15
   13d2e:	1530                	addi	a2,sp,680
   13d30:	2a3c                	fld	fa5,80(a2)
   13d32:	2c520b8f          	0x2c520b8f
   13d36:	1869                	addi	a6,a6,-6
   13d38:	135706b3          	0x135706b3
   13d3c:	2544                	fld	fs1,136(a0)
   13d3e:	0760                	addi	s0,sp,908
   13d40:	0eb4                	addi	a3,sp,856
   13d42:	201b0027          	0x201b0027
   13d46:	0820                	addi	s0,sp,24
   13d48:	09c6                	slli	s3,s3,0x11
   13d4a:	05bd                	addi	a1,a1,15
   13d4c:	2936                	fld	fs2,328(sp)
   13d4e:	2205                	jal	13e6e <iGMb+0x31e>
   13d50:	15e1                	addi	a1,a1,-8
   13d52:	0445                	addi	s0,s0,17
   13d54:	0ec8                	addi	a0,sp,852
   13d56:	13b1                	addi	t2,t2,-20
   13d58:	080a                	slli	a6,a6,0x2
   13d5a:	2cb820cf          	0x2cb820cf
   13d5e:	080b25a7          	fsw	ft0,139(s6)
   13d62:	2696                	fld	fa3,320(sp)
   13d64:	1ced                	addi	s9,s9,-5
   13d66:	09c0                	addi	s0,sp,212
   13d68:	1eee                	slli	t4,t4,0x3b
   13d6a:	2d4a                	fld	fs10,144(sp)
   13d6c:	1f390173          	0x1f390173
   13d70:	0c01                	addi	s8,s8,0
   13d72:	2856                	fld	fa6,336(sp)
   13d74:	0028                	addi	a0,sp,8
   13d76:	2714                	fld	fa3,8(a4)
   13d78:	241d                	jal	13f9e <iGMb+0x44e>
   13d7a:	15e31f33          	0x15e31f33
   13d7e:	1ed60fd3          	fdiv.q	ft11,fa2,fa3,rne
   13d82:	02a4                	addi	s1,sp,328
   13d84:	2c74                	fld	fa3,216(s0)
   13d86:	19651cd3          	fdiv.s	fs9,fa0,fs6,rtz
   13d8a:	1375                	addi	t1,t1,-3
   13d8c:	0a44                	addi	s1,sp,276
   13d8e:	0da0                	addi	s0,sp,728
   13d90:	2acc                	fld	fa1,144(a3)
   13d92:	1b6e                	slli	s6,s6,0x3b
   13d94:	1a51                	addi	s4,s4,-12
   13d96:	26cd                	jal	14178 <iGMb+0x628>
   13d98:	091a1be3          	bne	s4,a7,1462e <GMb+0x2de>
   13d9c:	0f2c                	addi	a1,sp,920
   13d9e:	1561                	addi	a0,a0,-8
   13da0:	1eb9                	addi	t4,t4,-18
   13da2:	1b1d                	addi	s6,s6,-25
   13da4:	1669                	addi	a2,a2,-6
   13da6:	15ed                	addi	a1,a1,-5
   13da8:	2521                	jal	143b0 <GMb+0x60>
   13daa:	2d30                	fld	fa2,88(a0)
   13dac:	2c0d                	jal	13fde <iGMb+0x48e>
   13dae:	09ce                	slli	s3,s3,0x13
   13db0:	1a21                	addi	s4,s4,-24
   13db2:	0182                	c.slli64	gp
   13db4:	116e                	slli	sp,sp,0x3b
   13db6:	0069                	c.nop	26
   13db8:	081c                	addi	a5,sp,16
   13dba:	007728cb          	fnmsub.s	fa7,fa4,ft7,ft0,rdn
   13dbe:	11120f73          	0x11120f73
   13dc2:	2cf1                	jal	1409e <iGMb+0x54e>
   13dc4:	0e58                	addi	a4,sp,788
   13dc6:	02ee2caf          	amoadd.w.rl	s9,a4,(t3)
   13dca:	0ca8                	addi	a0,sp,600
   13dcc:	0c3d                	addi	s8,s8,15
   13dce:	02f2                	slli	t0,t0,0x1c
   13dd0:	0fad                	addi	t6,t6,11
   13dd2:	2e99                	jal	14128 <iGMb+0x5d8>
   13dd4:	23fa                	fld	ft7,408(sp)
   13dd6:	1502                	slli	a0,a0,0x20
   13dd8:	2e69                	jal	14172 <iGMb+0x622>
   13dda:	2b0a                	fld	fs6,128(sp)
   13ddc:	0b02                	c.slli64	s6
   13dde:	1366073b          	0x1366073b
   13de2:	1ff5                	addi	t6,t6,-3
   13de4:	0a80                	addi	s0,sp,336
   13de6:	183d                	addi	a6,a6,-17
   13de8:	1a9e                	slli	s5,s5,0x27
   13dea:	039e                	slli	t2,t2,0x7
   13dec:	0b78                	addi	a4,sp,412
   13dee:	27bf10e7          	0x27bf10e7
   13df2:	1bb1                	addi	s7,s7,-20
   13df4:	179f 24c2 28fc      	0x28fc24c2179f
   13dfa:	22f6                	fld	ft5,344(sp)
   13dfc:	09a8                	addi	a0,sp,216
   13dfe:	02d8186f          	jal	a6,9562a <__BSS_END__+0x7da26>
   13e02:	1d91                	addi	s11,s11,-28
   13e04:	17a8                	addi	a0,sp,1000
   13e06:	28c0                	fld	fs0,144(s1)
   13e08:	2b1c                	fld	fa5,16(a4)
   13e0a:	0994                	addi	a3,sp,208
   13e0c:	0ecb0afb          	0xecb0afb
   13e10:	03b1                	addi	t2,t2,12
   13e12:	2326                	fld	ft6,72(sp)
   13e14:	04dc                	addi	a5,sp,580
   13e16:	2b09226f          	jal	tp,a60c6 <__BSS_END__+0x8e4c2>
   13e1a:	2bd2                	fld	fs7,272(sp)
   13e1c:	1706                	slli	a4,a4,0x21
   13e1e:	10e5                	addi	ra,ra,-7
   13e20:	121f 0eeb 2662      	0x26620eeb121f
   13e26:	1b90                	addi	a2,sp,496
   13e28:	1a82                	slli	s5,s5,0x20
   13e2a:	21de                	fld	ft3,464(sp)
   13e2c:	1e1b15a3          	sh	ra,491(s6)
   13e30:	0551                	addi	a0,a0,20
   13e32:	2654                	fld	fa3,136(a2)
   13e34:	0b85                	addi	s7,s7,1
   13e36:	2c01                	jal	14046 <iGMb+0x4f6>
   13e38:	283d                	jal	13e76 <iGMb+0x326>
   13e3a:	2394                	fld	fa3,0(a5)
   13e3c:	01de                	slli	gp,gp,0x17
   13e3e:	1959                	addi	s2,s2,-10
   13e40:	0065                	c.nop	25
   13e42:	250b0777          	0x250b0777
   13e46:	0e18                	addi	a4,sp,784
   13e48:	2edd                	jal	1423e <iGMb+0x6ee>
   13e4a:	2928                	fld	fa0,80(a0)
   13e4c:	032c                	addi	a1,sp,392
   13e4e:	027d22d3          	fadd.d	ft5,fs10,ft7,rdn
   13e52:	1fdf 14b3 23a8      	0x23a814b31fdf
   13e58:	0db8                	addi	a4,sp,728
   13e5a:	2062                	fld	ft0,24(sp)
   13e5c:	1b9c                	addi	a5,sp,496
   13e5e:	1ef2                	slli	t4,t4,0x3c
   13e60:	0bdc                	addi	a5,sp,468
   13e62:	08731297          	auipc	t0,0x8731
   13e66:	0f61                	addi	t5,t5,24
   13e68:	2c2a0eab          	0x2c2a0eab
   13e6c:	133a1e3b          	0x133a1e3b
   13e70:	2e9c                	fld	fa5,24(a3)
   13e72:	01a8                	addi	a0,sp,200
   13e74:	15a2                	slli	a1,a1,0x28
   13e76:	1854                	addi	a3,sp,52
   13e78:	1e622b7b          	0x1e622b7b
   13e7c:	2ec6                	fld	ft9,80(sp)
   13e7e:	0449                	addi	s0,s0,18
   13e80:	0b4a                	slli	s6,s6,0x12
   13e82:	0a09272b          	0xa09272b
   13e86:	08ca                	slli	a7,a7,0x12
   13e88:	0930                	addi	a2,sp,152
   13e8a:	0335                	addi	t1,t1,13
   13e8c:	09f6                	slli	s3,s3,0x1d
   13e8e:	2b08                	fld	fa0,16(a4)
   13e90:	1e59                	addi	t3,t3,-10
   13e92:	0088                	addi	a0,sp,64
   13e94:	0269                	addi	tp,tp,26
   13e96:	0c55                	addi	s8,s8,21
   13e98:	1701                	addi	a4,a4,-32
   13e9a:	1ac72403          	lw	s0,428(a4)
   13e9e:	0078                	addi	a4,sp,12
   13ea0:	1135                	addi	sp,sp,-19
   13ea2:	0721                	addi	a4,a4,8
   13ea4:	1c2e25a3          	sw	sp,459(t3)
   13ea8:	2815                	jal	13edc <iGMb+0x38c>
   13eaa:	2c81                	jal	140fa <iGMb+0x5aa>
   13eac:	0989                	addi	s3,s3,2
   13eae:	255a                	fld	fa0,400(sp)
   13eb0:	2ba8                	fld	fa0,80(a5)
   13eb2:	08250257          	0x8250257
   13eb6:	2cc9                	jal	14188 <iGMb+0x638>
   13eb8:	1c41                	addi	s8,s8,-16
   13eba:	1821                	addi	a6,a6,-24
   13ebc:	12c1                	addi	t0,t0,-16
   13ebe:	26c6                	fld	fa3,80(sp)
   13ec0:	2332                	fld	ft6,264(sp)
   13ec2:	11a2                	slli	gp,gp,0x28
   13ec4:	2c5824ef          	jal	s1,96988 <__BSS_END__+0x7ed84>
   13ec8:	2d96                	fld	fs11,320(sp)
   13eca:	181e                	slli	a6,a6,0x27
   13ecc:	1f0e                	slli	t5,t5,0x23
   13ece:	2626                	fld	fa2,72(sp)
   13ed0:	1af0                	addi	a2,sp,380
   13ed2:	0c8d2d53          	0xc8d2d53
   13ed6:	2119                	jal	142dc <iGMb+0x78c>
   13ed8:	2691                	jal	1421c <iGMb+0x6cc>
   13eda:	28b60b13          	addi	s6,a2,651 # 1c3a4f1f <__BSS_END__+0x1c38d31b>
   13ede:	0e94                	addi	a3,sp,848
   13ee0:	1f19                	addi	t5,t5,-26
   13ee2:	05b1                	addi	a1,a1,12
   13ee4:	2a69                	jal	1407e <iGMb+0x52e>
   13ee6:	1f85                	addi	t6,t6,-31
   13ee8:	0340                	addi	s0,sp,388
   13eea:	065c                	addi	a5,sp,772
   13eec:	0d52                	slli	s10,s10,0x14
   13eee:	1324                	addi	s1,sp,424
   13ef0:	13f72a67          	0x13f72a67
   13ef4:	18b52547          	fmsub.s	fa0,fa0,fa1,ft3,rdn
   13ef8:	0ff31d07          	0xff31d07
   13efc:	0c00                	addi	s0,sp,528
   13efe:	267d228f          	0x267d228f
   13f02:	278a                	fld	fa5,128(sp)
   13f04:	2c95148b          	0x2c95148b
   13f08:	199c                	addi	a5,sp,240
   13f0a:	05b9012f          	0x5b9012f
   13f0e:	0f1f 1309 16b5      	0x16b513090f1f
   13f14:	2721                	jal	1461c <GMb+0x2cc>
   13f16:	1af2                	slli	s5,s5,0x3c
   13f18:	173b0cef          	jal	s9,c488a <__BSS_END__+0xacc86>
   13f1c:	21bd                	jal	1438a <GMb+0x3a>
   13f1e:	16dc                	addi	a5,sp,868
   13f20:	0f10                	addi	a2,sp,912
   13f22:	03a0                	addi	s0,sp,456
   13f24:	1345                	addi	t1,t1,-15
   13f26:	2152                	fld	ft2,272(sp)
   13f28:	0888074f          	fnmadd.s	fa4,fa6,fs0,ft1,rne
   13f2c:	16f715c3          	fmadd.q	fa1,fa4,fa5,ft2,rtz
   13f30:	0d99                	addi	s11,s11,6
   13f32:	2d4d                	jal	145e4 <GMb+0x294>
   13f34:	1fd92527          	fsw	ft9,490(s2)
   13f38:	0a310023          	sb	gp,160(sp)
   13f3c:	1f80174b          	fnmsub.q	fa4,ft0,fs8,ft3,rtz
   13f40:	0438                	addi	a4,sp,520
   13f42:	20fc2f07          	flw	ft10,527(s8)
   13f46:	0bec                	addi	a1,sp,476
   13f48:	0ee5                	addi	t4,t4,25
   13f4a:	2b39                	jal	14468 <GMb+0x118>
   13f4c:	1a50                	addi	a2,sp,308
   13f4e:	2106                	fld	ft2,64(sp)
   13f50:	0924                	addi	s1,sp,152
   13f52:	07761de3          	bne	a2,s7,147cc <GMb+0x47c>
   13f56:	29d5                	jal	1444a <GMb+0xfa>
   13f58:	0845                	addi	a6,a6,17
   13f5a:	25a5                	jal	145c2 <GMb+0x272>
   13f5c:	1902                	slli	s2,s2,0x20
   13f5e:	178c                	addi	a1,sp,992
   13f60:	084c                	addi	a1,sp,20
   13f62:	1e15                	addi	t3,t3,-27
   13f64:	143f0a77          	0x143f0a77
   13f68:	187e                	slli	a6,a6,0x3f
   13f6a:	1d00                	addi	s0,sp,688
   13f6c:	0a25                	addi	s4,s4,9
   13f6e:	24061a8b          	0x24061a8b
   13f72:	2a55                	jal	14126 <iGMb+0x5d6>
   13f74:	0118                	addi	a4,sp,128
   13f76:	0cc62187          	flw	ft3,204(a2)
   13f7a:	1a61                	addi	s4,s4,-8
   13f7c:	0932                	slli	s2,s2,0xc
   13f7e:	17d60ec3          	fmadd.q	ft9,fa2,ft9,ft2,rne
   13f82:	127c                	addi	a5,sp,300
   13f84:	1726                	slli	a4,a4,0x29
   13f86:	09c1                	addi	s3,s3,16
   13f88:	21c0                	fld	fs0,128(a1)
   13f8a:	2831                	jal	13fa6 <iGMb+0x456>
   13f8c:	2f5f17db          	0x2f5f17db
   13f90:	0b8e                	slli	s7,s7,0x3
   13f92:	2fff                	0x2fff
   13f94:	2834                	fld	fa3,80(s0)
   13f96:	1f96                	slli	t6,t6,0x25
   13f98:	0331                	addi	t1,t1,12
   13f9a:	0fb5                	addi	t6,t6,13
   13f9c:	0a32                	slli	s4,s4,0xc
   13f9e:	05a4                	addi	s1,sp,712
   13fa0:	2dc8170b          	0x2dc8170b
   13fa4:	0cdc                	addi	a5,sp,596
   13fa6:	0978                	addi	a4,sp,156
   13fa8:	13e2                	slli	t2,t2,0x38
   13faa:	1c4a                	slli	s8,s8,0x32
   13fac:	1455                	addi	s0,s0,-11
   13fae:	14a1                	addi	s1,s1,-24
   13fb0:	26e4                	fld	fs1,200(a3)
   13fb2:	0a8e                	slli	s5,s5,0x3
   13fb4:	1a00                	addi	s0,sp,304
   13fb6:	02df 08c3 2d88      	0x2d8808c302df
   13fbc:	0341                	addi	t1,t1,16
   13fbe:	177c0c23          	sb	s7,376(s8)
   13fc2:	1a91                	addi	s5,s5,-28
   13fc4:	0466                	slli	s0,s0,0x19
   13fc6:	148218c3          	0x148218c3
   13fca:	25aa2897          	auipc	a7,0x25aa2
   13fce:	149e                	slli	s1,s1,0x27
   13fd0:	0db9                	addi	s11,s11,14
   13fd2:	2629                	jal	142dc <iGMb+0x78c>
   13fd4:	0bd1                	addi	s7,s7,20
   13fd6:	24d9030b          	0x24d9030b
   13fda:	0d40                	addi	s0,sp,660
   13fdc:	1d0d                	addi	s10,s10,-29
   13fde:	029c                	addi	a5,sp,320
   13fe0:	27c8                	fld	fa0,136(a5)
   13fe2:	197f1faf          	0x197f1faf
   13fe6:	19a8                	addi	a0,sp,248
   13fe8:	19522a4f          	fnmadd.s	fs4,ft4,fs5,ft3,rdn
   13fec:	164f2047          	fmsub.q	ft0,ft10,ft4,ft2,rdn
   13ff0:	2634                	fld	fa3,72(a2)
   13ff2:	155601d3          	0x155601d3
   13ff6:	1149                	addi	sp,sp,-14
   13ff8:	2edf 04b5 1397      	0x139704b52edf
   13ffe:	1b06                	slli	s6,s6,0x21
   14000:	13e8                	addi	a0,sp,492
   14002:	15950ef3          	0x15950ef3
   14006:	0dbe2d3b          	0xdbe2d3b
   1400a:	1cdc130b          	0x1cdc130b
   1400e:	19d7078b          	0x19d7078b
   14012:	0605                	addi	a2,a2,1
   14014:	2204                	fld	fs1,0(a2)
   14016:	0104                	addi	s1,sp,128
   14018:	0d39                	addi	s10,s10,14
   1401a:	12b8                	addi	a4,sp,360
   1401c:	16411127          	0x16411127
   14020:	086b1ed7          	0x86b1ed7
   14024:	1ca9                	addi	s9,s9,-22
   14026:	00ec                	addi	a1,sp,76
   14028:	2d0e298b          	0x2d0e298b
   1402c:	0772                	slli	a4,a4,0x1c
   1402e:	12b9                	addi	t0,t0,-18
   14030:	1c472537          	lui	a0,0x1c472
   14034:	20a2                	fld	ft1,8(sp)
   14036:	1401                	addi	s0,s0,-32
   14038:	29a6                	fld	fs3,72(sp)
   1403a:	0d120907          	0xd120907
   1403e:	216c                	fld	fa1,192(a0)
   14040:	044002c3          	0x44002c3
   14044:	1348                	addi	a0,sp,420
   14046:	02a6                	slli	t0,t0,0x9
   14048:	2805                	jal	14078 <iGMb+0x528>
   1404a:	0012                	c.slli	zero,0x4
   1404c:	1634                	addi	a3,sp,808
   1404e:	03c0                	addi	s0,sp,452
   14050:	1f15116b          	0x1f15116b
   14054:	00e2                	slli	ra,ra,0x18
   14056:	00060993          	mv	s3,a2
   1405a:	22aa                	fld	ft5,136(sp)
   1405c:	0140                	addi	s0,sp,132
   1405e:	189a                	slli	a7,a7,0x26
   14060:	221f2303          	lw	t1,545(t5)
   14064:	0b24                	addi	s1,sp,408
   14066:	0ba5                	addi	s7,s7,9
   14068:	152006ab          	0x152006ab
   1406c:	1399                	addi	t2,t2,-26
   1406e:	2694                	fld	fa3,8(a3)
   14070:	263e                	fld	fa2,456(sp)
   14072:	0b98                	addi	a4,sp,464
   14074:	1a49076b          	0x1a49076b
   14078:	14aa1057          	0x14aa1057
   1407c:	2764                	fld	fs1,200(a4)
   1407e:	1dff                	0x1dff
   14080:	1f05                	addi	t5,t5,-31
   14082:	2228                	fld	fa0,64(a2)
   14084:	163e                	slli	a2,a2,0x2f
   14086:	0d85                	addi	s11,s11,1
   14088:	1673104f          	fnmadd.q	ft0,ft6,ft7,ft2,rtz
   1408c:	15b9                	addi	a1,a1,-18
   1408e:	0d32                	slli	s10,s10,0xc
   14090:	03b8146b          	0x3b8146b
   14094:	10df 2652 1104      	0x1104265210df
   1409a:	0c10                	addi	a2,sp,528
   1409c:	2b6e                	fld	fs6,216(sp)
   1409e:	0348                	addi	a0,sp,388
   140a0:	1871                	addi	a6,a6,-4
   140a2:	01e6                	slli	gp,gp,0x19
   140a4:	1770                	addi	a2,sp,940
   140a6:	053e                	slli	a0,a0,0xf
   140a8:	288e                	fld	fa7,192(sp)
   140aa:	1781                	addi	a5,a5,-32
   140ac:	12be                	slli	t0,t0,0x2f
   140ae:	1571                	addi	a0,a0,-4
   140b0:	1192                	slli	gp,gp,0x24
   140b2:	1061                	c.nop	-8
   140b4:	0902                	c.slli64	s2
   140b6:	1979                	addi	s2,s2,-2
   140b8:	18e405c3          	fmadd.s	fa1,fs0,fa4,ft3,rne
   140bc:	2345                	jal	1465c <GMb+0x30c>
   140be:	1f65                	addi	t5,t5,-7
   140c0:	0659                	addi	a2,a2,22
   140c2:	1b6c                	addi	a1,sp,444
   140c4:	1284                	addi	s1,sp,352
   140c6:	1662                	slli	a2,a2,0x38
   140c8:	1f14                	addi	a3,sp,944
   140ca:	195e18cf          	fnmadd.s	fa7,ft8,fs5,ft3,rtz
   140ce:	1b05                	addi	s6,s6,-31
   140d0:	2c8d                	jal	14342 <iGMb+0x7f2>
   140d2:	27da1d3f 1df227ab 	0x1df227ab27da1d3f
   140da:	1d84                	addi	s1,sp,752
   140dc:	2cf5                	jal	143d8 <GMb+0x88>
   140de:	060a                	slli	a2,a2,0x2
   140e0:	27d719ab          	0x27d719ab
   140e4:	08d9                	addi	a7,a7,22
   140e6:	1c9f 16c0 2c84      	0x2c8416c01c9f
   140ec:	2d3d                	jal	1472a <GMb+0x3da>
   140ee:	25fa                	fld	fa1,408(sp)
   140f0:	2bbf08cb          	fnmsub.d	fa7,ft10,fs11,ft5,rne
   140f4:	14ec                	addi	a1,sp,620
   140f6:	1cf0                	addi	a2,sp,636
   140f8:	0b2d                	addi	s6,s6,11
   140fa:	23ff0fa3          	sb	t6,575(t5)
   140fe:	01e4                	addi	s1,sp,204
   14100:	1d66                	slli	s10,s10,0x39
   14102:	24c1                	jal	143c2 <GMb+0x72>
   14104:	180d2fcb          	fnmsub.s	ft11,fs10,ft0,ft3,rdn
   14108:	2341                	jal	14688 <GMb+0x338>
   1410a:	0849                	addi	a6,a6,18
   1410c:	09d7280f          	0x9d7280f
   14110:	253d                	jal	1473e <GMb+0x3ee>
   14112:	0ef0                	addi	a2,sp,860
   14114:	21e2                	fld	ft3,24(sp)
   14116:	2a882c9b          	0x2a882c9b
   1411a:	129a                	slli	t0,t0,0x26
   1411c:	10012c27          	fsw	ft0,280(sp)
   14120:	096e                	slli	s2,s2,0x1b
   14122:	1960                	addi	s0,sp,188
   14124:	26e1                	jal	144ec <GMb+0x19c>
   14126:	293a                	fld	fs2,392(sp)
   14128:	0328                	addi	a0,sp,392
   1412a:	08520bb7          	lui	s7,0x8520
   1412e:	10be                	slli	ra,ra,0x2f
   14130:	2f2e                	fld	ft10,200(sp)
   14132:	1d15                	addi	s10,s10,-27
   14134:	140c                	addi	a1,sp,544
   14136:	00f51eeb          	0xf51eeb
   1413a:	1756                	slli	a4,a4,0x35
   1413c:	130a                	slli	t1,t1,0x22
   1413e:	1c7c                	addi	a5,sp,572
   14140:	1d88                	addi	a0,sp,752
   14142:	26e0292b          	0x26e0292b
   14146:	08412373          	csrrs	t1,0x84,sp
   1414a:	0e89                	addi	t4,t4,2
   1414c:	282d                	jal	14186 <iGMb+0x636>
   1414e:	2726                	fld	fa4,72(sp)
   14150:	256a                	fld	fa0,152(sp)
   14152:	22e6                	fld	ft5,88(sp)
   14154:	2b42                	fld	fs6,16(sp)
   14156:	251a                	fld	fa0,384(sp)
   14158:	0126                	slli	sp,sp,0x9
   1415a:	0d3f1267          	0xd3f1267
   1415e:	0561                	addi	a0,a0,24
   14160:	2370                	fld	fa2,192(a4)
   14162:	27cd                	jal	14944 <GMb+0x5f4>
   14164:	11d9                	addi	gp,gp,-10
   14166:	2a8a                	fld	fs5,128(sp)
   14168:	26b5                	jal	144d4 <GMb+0x184>
   1416a:	00351b0b          	0x351b0b
   1416e:	122d                	addi	tp,tp,-21
   14170:	280d01b7          	lui	gp,0x280d0
   14174:	1b74                	addi	a3,sp,444
   14176:	27df 2097 0475      	0x475209727df
   1417c:	09fc                	addi	a5,sp,220
   1417e:	1db1                	addi	s11,s11,-20
   14180:	1fd6                	slli	t6,t6,0x35
   14182:	2986                	fld	fs3,64(sp)
   14184:	21c8                	fld	fa0,128(a1)
   14186:	2668                	fld	fa0,200(a2)
   14188:	2bed1f0f          	0x2bed1f0f
   1418c:	16850853          	fmul.q	fa6,fa0,fs0,rne
   14190:	26352867          	0x26352867
   14194:	0a9e                	slli	s5,s5,0x7
   14196:	11b3058b          	0x11b3058b
   1419a:	0f04                	addi	s1,sp,912
   1419c:	0fe2                	slli	t6,t6,0x18
   1419e:	10c5                	addi	ra,ra,-15
   141a0:	2d89                	jal	147f2 <GMb+0x4a2>
   141a2:	2d05                	jal	147d2 <GMb+0x482>
   141a4:	2c59                	jal	1443a <GMb+0xea>
   141a6:	10d9                	addi	ra,ra,-10
   141a8:	1305                	addi	t1,t1,-31
   141aa:	2f9a                	fld	ft11,384(sp)
   141ac:	2a8c064b          	fnmsub.d	fa2,fs8,fs0,ft5,rne
   141b0:	2ce1                	jal	14488 <GMb+0x138>
   141b2:	2281                	jal	142f2 <iGMb+0x7a2>
   141b4:	0959                	addi	s2,s2,22
   141b6:	2a4e000f          	0x2a4e000f
   141ba:	0011138b          	0x11138b
   141be:	0235                	addi	tp,tp,13
   141c0:	2f911703          	lh	a4,761(sp)
   141c4:	2b32                	fld	fs6,264(sp)
   141c6:	28ac                	fld	fa1,80(s1)
   141c8:	22b5                	jal	14334 <iGMb+0x7e4>
   141ca:	0f86                	slli	t6,t6,0x1
   141cc:	2ae5                	jal	143c4 <GMb+0x74>
   141ce:	1bda                	slli	s7,s7,0x36
   141d0:	16d0                	addi	a2,sp,868
   141d2:	28f2                	fld	fa7,280(sp)
   141d4:	2092                	fld	ft1,256(sp)
   141d6:	1b341793          	0x1b341793
   141da:	0626                	slli	a2,a2,0x9
   141dc:	2ab8                	fld	fa4,80(a3)
   141de:	07e4                	addi	s1,sp,972
   141e0:	09a1                	addi	s3,s3,8
   141e2:	1fff                	0x1fff
   141e4:	0180                	addi	s0,sp,192
   141e6:	0a52                	slli	s4,s4,0x14
   141e8:	0aa9                	addi	s5,s5,10
   141ea:	087f1517          	auipc	a0,0x87f1
   141ee:	24b4                	fld	fa3,72(s1)
   141f0:	1f632ed3          	fdiv.q	ft9,ft6,fs6,rdn
   141f4:	19d31117          	auipc	sp,0x19d31
   141f8:	1392                	slli	t2,t2,0x24
   141fa:	2e24                	fld	fs1,88(a2)
   141fc:	2ca323ab          	0x2ca323ab
   14200:	0068                	addi	a0,sp,12
   14202:	18cc                	addi	a1,sp,116
   14204:	1a6525ab          	0x1a6525ab
   14208:	2f4e                	fld	ft10,208(sp)
   1420a:	15f1                	addi	a1,a1,-4
   1420c:	021d2ab7          	lui	s5,0x21d2
   14210:	0be10087          	0xbe10087
   14214:	1c20                	addi	s0,sp,568
   14216:	197e                	slli	s2,s2,0x3f
   14218:	13dd                	addi	t2,t2,-9
   1421a:	2f68                	fld	fa0,216(a4)
   1421c:	034a                	slli	t1,t1,0x12
   1421e:	1021                	c.nop	-24
   14220:	1e05                	addi	t3,t3,-31
   14222:	20ea2b47          	fmsub.s	fs6,fs4,fa4,ft4,rdn
   14226:	03f0                	addi	a2,sp,460
   14228:	0aa5                	addi	s5,s5,9
   1422a:	2dfc                	fld	fa5,216(a1)
   1422c:	17aa                	slli	a5,a5,0x2a
   1422e:	044d                	addi	s0,s0,19
   14230:	079e                	slli	a5,a5,0x7
   14232:	20e8                	fld	fa0,192(s1)
   14234:	1638                	addi	a4,sp,808
   14236:	1adc                	addi	a5,sp,372
   14238:	2ee5                	jal	14630 <GMb+0x2e0>
   1423a:	275f 14d7 039f      	0x39f14d7275f
   14240:	06ea                	slli	a3,a3,0x1a
   14242:	0111                	addi	sp,sp,4
   14244:	20b9                	jal	14292 <iGMb+0x742>
   14246:	08df 1469 282b      	0x282b146908df
   1424c:	0074                	addi	a3,sp,12
   1424e:	2e1f 005b 2db3      	0x2db3005b2e1f
   14254:	02f5                	addi	t0,t0,29
   14256:	0518                	addi	a4,sp,640
   14258:	1d64                	addi	s1,sp,700
   1425a:	1f601933          	0x1f601933
   1425e:	1fda                	slli	t6,t6,0x36
   14260:	1d20                	addi	s0,sp,696
   14262:	105f 0135 090e      	0x90e0135105f
   14268:	08f4                	addi	a3,sp,92
   1426a:	2899                	jal	142c0 <iGMb+0x770>
   1426c:	25092d77          	0x25092d77
   14270:	2fce                	fld	ft11,208(sp)
   14272:	2962                	fld	fs2,24(sp)
   14274:	2561                	jal	148fc <GMb+0x5ac>
   14276:	1ee8                	addi	a0,sp,892
   14278:	2880                	fld	fs0,16(s1)
   1427a:	26a1                	jal	145c2 <GMb+0x272>
   1427c:	2fd4                	fld	fa3,152(a5)
   1427e:	0f541c0b          	0xf541c0b
   14282:	0c74                	addi	a3,sp,540
   14284:	081d016f          	jal	sp,e4b04 <__BSS_END__+0xccf00>
   14288:	0150                	addi	a2,sp,132
   1428a:	1508                	addi	a0,sp,672
   1428c:	15ff                	0x15ff
   1428e:	2194                	fld	fa3,0(a1)
   14290:	120d                	addi	tp,tp,-29
   14292:	22a206ef          	jal	a3,344bc <__BSS_END__+0x1c8b8>
   14296:	17dc01c3          	fmadd.q	ft3,fs8,ft9,ft2,rne
   1429a:	0525                	addi	a0,a0,9
   1429c:	1866                	slli	a6,a6,0x39
   1429e:	1708225b          	0x1708225b
   142a2:	0c3c1c73          	csrrw	s8,0xc3,s8
   142a6:	2d2c                	fld	fa1,88(a0)
   142a8:	1371                	addi	t1,t1,-4
   142aa:	2f81                	jal	149fa <GMb+0x6aa>
   142ac:	05561ccb          	0x5561ccb
   142b0:	2f62                	fld	ft10,24(sp)
   142b2:	0ee1297b          	0xee1297b
   142b6:	141d                	addi	s0,s0,-25
   142b8:	189c                	addi	a5,sp,112
   142ba:	0a4e                	slli	s4,s4,0x13
   142bc:	1065                	c.nop	-7
   142be:	058a                	slli	a1,a1,0x2
   142c0:	2751                	jal	14a44 <GMb+0x6f4>
   142c2:	103c                	addi	a5,sp,40
   142c4:	20b5                	jal	14330 <iGMb+0x7e0>
   142c6:	21c4                	fld	fs1,128(a1)
   142c8:	28cd                	jal	143ba <GMb+0x6a>
   142ca:	0372                	slli	t1,t1,0x1c
   142cc:	1fde                	slli	t6,t6,0x37
   142ce:	27bd                	jal	14a3c <GMb+0x6ec>
   142d0:	2f9f2623          	sw	s9,748(t5)
   142d4:	0b9601cb          	fnmsub.d	ft3,fa2,fs9,ft1,rne
   142d8:	0c5e                	slli	s8,s8,0x17
   142da:	0195                	addi	gp,gp,5
   142dc:	1388                	addi	a0,sp,480
   142de:	245f 1904 231a      	0x231a1904245f
   142e4:	1fef060f          	0x1fef060f
   142e8:	0e2e                	slli	t3,t3,0xb
   142ea:	2a0e                	fld	fs4,192(sp)
   142ec:	2431                	jal	144f8 <GMb+0x1a8>
   142ee:	02bc                	addi	a5,sp,328
   142f0:	217d                	jal	1479e <GMb+0x44e>
   142f2:	2524                	fld	fs1,72(a0)
   142f4:	19e6                	slli	s3,s3,0x39
   142f6:	2cad                	jal	14570 <GMb+0x220>
   142f8:	16da2d4b          	fnmsub.q	fs10,fs4,fa3,ft2,rdn
   142fc:	0f6e                	slli	t5,t5,0x1b
   142fe:	2ea512a7          	0x2ea512a7
   14302:	05a6                	slli	a1,a1,0x9
   14304:	1782                	slli	a5,a5,0x20
   14306:	0d3a                	slli	s10,s10,0xe
   14308:	2cce                	fld	fs9,208(sp)
   1430a:	14be                	slli	s1,s1,0x2f
   1430c:	1564                	addi	s1,sp,684
   1430e:	0229                	addi	tp,tp,10
   14310:	2502                	fld	fa0,0(sp)
   14312:	0a1a                	slli	s4,s4,0x6
   14314:	0ab50597          	auipc	a1,0xab50
   14318:	01d9                	addi	gp,gp,22
   1431a:	12892c77          	0x12892c77
   1431e:	0344                	addi	s1,sp,388
   14320:	0fde                	slli	t6,t6,0x17
   14322:	29aa                	fld	fs3,136(sp)
   14324:	2de81e2f          	0x2de81e2f
   14328:	159e                	slli	a1,a1,0x27
   1432a:	0138                	addi	a4,sp,136
   1432c:	10ff10d3          	fmul.s	ft1,ft10,fa5,rtz
   14330:	1684                	addi	s1,sp,864
   14332:	20bd21e7          	0x20bd21e7
   14336:	00051ffb          	0x51ffb
   1433a:	110b1ce3          	bne	s6,a6,14c52 <h+0x102>
   1433e:	0480                	addi	s0,sp,576
   14340:	152d                	addi	a0,a0,-21
   14342:	1949146f          	jal	s0,a54d6 <__BSS_END__+0x8d8d2>
   14346:	01b4                	addi	a3,sp,200
   14348:	219b1d8f          	0x219b1d8f
   1434c:	1855                	addi	a6,a6,-11
   1434e:	2026                	fld	ft0,72(sp)

00014350 <GMb>:
   14350:	1ed00ffb          	0x1ed00ffb
   14354:	2b34                	fld	fa3,80(a4)
   14356:	2bc8                	fld	fa0,144(a5)
   14358:	1b30                	addi	a2,sp,440
   1435a:	10f6                	slli	ra,ra,0x3d
   1435c:	261f1883          	lh	a7,609(t5)
   14360:	18ff0637          	lui	a2,0x18ff0
   14364:	2505                	jal	14984 <GMb+0x634>
   14366:	1492                	slli	s1,s1,0x24
   14368:	024a                	slli	tp,tp,0x12
   1436a:	16c1                	addi	a3,a3,-16
   1436c:	1d72                	slli	s10,s10,0x3c
   1436e:	25ee                	fld	fa1,216(sp)
   14370:	046e                	slli	s0,s0,0x1b
   14372:	06af1907          	0x6af1907
   14376:	03c5                	addi	t2,t2,17
   14378:	1dfa1bbb          	0x1dfa1bbb
   1437c:	0e9f 192a 28ae      	0x28ae192a0e9f
   14382:	1fa4                	addi	s1,sp,1016
   14384:	075d                	addi	a4,a4,23
   14386:	0698                	addi	a4,sp,832
   14388:	0554                	addi	a3,sp,644
   1438a:	2859                	jal	14420 <GMb+0xd0>
   1438c:	27b4                	fld	fa3,72(a5)
   1438e:	23dc                	fld	fa5,128(a5)
   14390:	2fb2                	fld	ft11,264(sp)
   14392:	1860                	addi	s0,sp,60
   14394:	03e5                	addi	t2,t2,25
   14396:	0075                	c.nop	29
   14398:	113712af          	0x113712af
   1439c:	060d                	addi	a2,a2,3
   1439e:	1ba0                	addi	s0,sp,504
   143a0:	0b0d                	addi	s6,s6,3
   143a2:	193a                	slli	s2,s2,0x2e
   143a4:	22ad114f          	fnmadd.d	ft2,fs10,fa0,ft4,rtz
   143a8:	1be8                	addi	a0,sp,508
   143aa:	0a04                	addi	s1,sp,272
   143ac:	1620                	addi	s0,sp,808
   143ae:	0fca                	slli	t6,t6,0x12
   143b0:	2f9d                	jal	14b26 <GMb+0x7d6>
   143b2:	01b0                	addi	a2,sp,200
   143b4:	29ff                	0x29ff
   143b6:	04d5                	addi	s1,s1,21
   143b8:	1dba                	slli	s11,s11,0x2e
   143ba:	05fe                	slli	a1,a1,0x1f
   143bc:	1eb70f8f          	0x1eb70f8f
   143c0:	0885                	addi	a7,a7,1
   143c2:	18a4                	addi	s1,sp,120
   143c4:	2210                	fld	fa2,0(a2)
   143c6:	19aa                	slli	s3,s3,0x2a
   143c8:	069a12eb          	0x69a12eb
   143cc:	000e                	c.slli	zero,0x3
   143ce:	0f20                	addi	s0,sp,920
   143d0:	15c1                	addi	a1,a1,-16
   143d2:	2498                	fld	fa4,8(s1)
   143d4:	07e32f83          	lw	t6,126(t1)
   143d8:	090b1d77          	0x90b1d77
   143dc:	1241                	addi	tp,tp,-16
   143de:	1cac                	addi	a1,sp,632
   143e0:	0611                	addi	a2,a2,4
   143e2:	0484                	addi	s1,sp,576
   143e4:	20d1                	jal	144a8 <GMb+0x158>
   143e6:	2c7d                	jal	146a4 <GMb+0x354>
   143e8:	03fc                	addi	a5,sp,460
   143ea:	2a140b97          	auipc	s7,0x2a140
   143ee:	1b85                	addi	s7,s7,-31
   143f0:	0cf4                	addi	a3,sp,604
   143f2:	2be4                	fld	fs1,208(a5)
   143f4:	14a5                	addi	s1,s1,-23
   143f6:	2d3a                	fld	fs10,392(sp)
   143f8:	298d                	jal	1486a <GMb+0x51a>
   143fa:	2766                	fld	fa4,88(sp)
   143fc:	2515                	jal	14a20 <GMb+0x6d0>
   143fe:	1824                	addi	s1,sp,56
   14400:	243d                	jal	1462e <GMb+0x2de>
   14402:	17f2                	slli	a5,a5,0x3c
   14404:	03730cfb          	0x3730cfb
   14408:	28e5                	jal	14500 <GMb+0x1b0>
   1440a:	01e9                	addi	gp,gp,26
   1440c:	05de                	slli	a1,a1,0x17
   1440e:	2b350b23          	sb	s3,694(a0) # 88054a0 <__BSS_END__+0x87ed89c>
   14412:	2601                	jal	14712 <GMb+0x3c2>
   14414:	0ab6                	slli	s5,s5,0xd
   14416:	2fd1                	jal	14bea <h+0x9a>
   14418:	136a                	slli	t1,t1,0x3a
   1441a:	28f1                	jal	144f6 <GMb+0x1a6>
   1441c:	275e                	fld	fa4,464(sp)
   1441e:	02da04ab          	0x2da04ab
   14422:	06e2                	slli	a3,a3,0x18
   14424:	0f0e                	slli	t5,t5,0x3
   14426:	07ee                	slli	a5,a5,0x1b
   14428:	1704                	addi	s1,sp,928
   1442a:	2aaa                	fld	fs5,136(sp)
   1442c:	233c                	fld	fa5,64(a4)
   1442e:	149a                	slli	s1,s1,0x26
   14430:	0e1423db          	0xe1423db
   14434:	0ec6                	slli	t4,t4,0x11
   14436:	27de                	fld	fa5,464(sp)
   14438:	0c6c                	addi	a1,sp,540
   1443a:	123c0d8b          	0x123c0d8b
   1443e:	098e                	slli	s3,s3,0x3
   14440:	1dbd                	addi	s11,s11,-17
   14442:	24aa                	fld	fs1,136(sp)
   14444:	0342                	slli	t1,t1,0x10
   14446:	1ab41e17          	auipc	t3,0x1ab41
   1444a:	14e70d4b          	0x14e70d4b
   1444e:	2ff4                	fld	fa3,216(a5)
   14450:	0dfc                	addi	a5,sp,732
   14452:	2a4406cb          	fnmsub.d	fa3,fs0,ft4,ft5,rne
   14456:	27e1263b          	0x27e1263b
   1445a:	0fe6                	slli	t6,t6,0x19
   1445c:	2fda                	fld	ft11,400(sp)
   1445e:	214d                	jal	14900 <GMb+0x5b0>
   14460:	28a1                	jal	144b8 <GMb+0x168>
   14462:	0abd                	addi	s5,s5,15
   14464:	1caa                	slli	s9,s9,0x2a
   14466:	294e                	fld	fs2,208(sp)
   14468:	1798                	addi	a4,sp,992
   1446a:	247203af          	0x247203af
   1446e:	05c5                	addi	a1,a1,17
   14470:	1ad1                	addi	s5,s5,-12
   14472:	25c4                	fld	fs1,136(a1)
   14474:	0e01                	addi	t3,t3,0
   14476:	19e9                	addi	s3,s3,-6
   14478:	2f71                	jal	14c14 <h+0xc4>
   1447a:	0fdf 0e64 1e00      	0x1e000e640fdf
   14480:	1ffc                	addi	a5,sp,1020
   14482:	1af6                	slli	s5,s5,0x3d
   14484:	0dcd                	addi	s11,s11,19
   14486:	17ca264f          	fnmadd.q	fa2,fs4,ft8,ft2,rdn
   1448a:	277302d7          	0x277302d7
   1448e:	1b211b5b          	0x1b211b5b
   14492:	079d                	addi	a5,a5,7
   14494:	293f2603          	lw	a2,659(t5)
   14498:	17a9                	addi	a5,a5,-22
   1449a:	017a                	slli	sp,sp,0x1e
   1449c:	223b1ebf 240d22c5 	0x240d22c5223b1ebf
   144a4:	228e                	fld	ft5,192(sp)
   144a6:	257511c7          	0x257511c7
   144aa:	2d90                	fld	fa2,24(a1)
   144ac:	1dce                	slli	s11,s11,0x33
   144ae:	2275                	jal	1465a <GMb+0x30a>
   144b0:	1630                	addi	a2,sp,808
   144b2:	135c                	addi	a5,sp,420
   144b4:	20c4186b          	0x20c4186b
   144b8:	27ac                	fld	fa1,72(a5)
   144ba:	09252213          	slti	tp,a0,146
   144be:	05bb0c57          	0x5bb0c57
   144c2:	1554                	addi	a3,sp,676
   144c4:	2169                	jal	1494e <GMb+0x5fe>
   144c6:	0a591e67          	0xa591e67
   144ca:	0910                	addi	a2,sp,144
   144cc:	234c                	fld	fa1,128(a4)
   144ce:	182c                	addi	a1,sp,56
   144d0:	02e1                	addi	t0,t0,24
   144d2:	0e72                	slli	t3,t3,0x1c
   144d4:	1679125b          	0x1679125b
   144d8:	2356                	fld	ft6,336(sp)
   144da:	00100e67          	jalr	t3,1(zero) # 0 <main-0x10074>
   144de:	0392                	slli	t2,t2,0x4
   144e0:	1442                	slli	s0,s0,0x30
   144e2:	11c82923          	sw	t3,274(a6) # 9b21112 <__BSS_END__+0x9b0950e>
   144e6:	07ac                	addi	a1,sp,968
   144e8:	0db5                	addi	s11,s11,13
   144ea:	20f4                	fld	fa3,192(s1)
   144ec:	1d5c                	addi	a5,sp,692
   144ee:	1505                	addi	a0,a0,-31
   144f0:	29ed                	jal	149ea <GMb+0x69a>
   144f2:	0cd1                	addi	s9,s9,20
   144f4:	1b7d                	addi	s6,s6,-1
   144f6:	0424                	addi	s1,sp,520
   144f8:	1bf40b4f          	fnmadd.d	fs6,fs0,ft11,ft3,rne
   144fc:	14ed22b7          	lui	t0,0x14ed2
   14500:	1909                	addi	s2,s2,-30
   14502:	2005                	jal	14522 <GMb+0x1d2>
   14504:	0b92                	slli	s7,s7,0x4
   14506:	13c818e7          	0x13c818e7
   1450a:	19ea                	slli	s3,s3,0x3a
   1450c:	15f9                	addi	a1,a1,-2
   1450e:	0116                	slli	sp,sp,0x5
   14510:	03a4                	addi	s1,sp,456
   14512:	27f5                	jal	14cfe <h+0x1ae>
   14514:	22df 1dda 015f      	0x15f1dda22df
   1451a:	2452                	fld	fs0,272(sp)
   1451c:	00ed                	addi	ra,ra,27
   1451e:	16e2                	slli	a3,a3,0x38
   14520:	1e0c                	addi	a1,sp,816
   14522:	0c4a                	slli	s8,s8,0x12
   14524:	2f5e                	fld	ft10,464(sp)
   14526:	1da2                	slli	s11,s11,0x28
   14528:	0805                	addi	a6,a6,1
   1452a:	2c15                	jal	1475e <GMb+0x40e>
   1452c:	0eda                	slli	t4,t4,0x16
   1452e:	1454                	addi	a3,sp,548
   14530:	11fa                	slli	gp,gp,0x3e
   14532:	06d4                	addi	a3,sp,836
   14534:	2c24                	fld	fs1,88(s0)
   14536:	0154                	addi	a3,sp,132
   14538:	0e7f                	0xe7f
   1453a:	1206                	slli	tp,tp,0x21
   1453c:	012c                	addi	a1,sp,136
   1453e:	2af1                	jal	1471a <GMb+0x3ca>
   14540:	13ce                	slli	t2,t2,0x33
   14542:	2741                	jal	14cc2 <h+0x172>
   14544:	2d60                	fld	fs0,216(a0)
   14546:	1cfd2fd7          	0x1cfd2fd7
   1454a:	167229d3          	fmul.q	fs3,ft4,ft7,rdn
   1454e:	1616                	slli	a2,a2,0x25
   14550:	15b10efb          	0x15b10efb
   14554:	04c8                	addi	a0,sp,580
   14556:	211c                	fld	fa5,0(a0)
   14558:	2415                	jal	1477c <GMb+0x42c>
   1455a:	0f05                	addi	t5,t5,1
   1455c:	00fa                	slli	ra,ra,0x1e
   1455e:	2bc9                	jal	14b30 <GMb+0x7e0>
   14560:	1081                	addi	ra,ra,-32
   14562:	18b6                	slli	a7,a7,0x2d
   14564:	25d0                	fld	fa2,136(a1)
   14566:	2fde                	fld	ft11,464(sp)
   14568:	1028                	addi	a0,sp,40
   1456a:	0ada                	slli	s5,s5,0x16
   1456c:	02b4                	addi	a3,sp,328
   1456e:	2268                	fld	fa0,192(a2)
   14570:	190a                	slli	s2,s2,0x22
   14572:	1a3e                	slli	s4,s4,0x2f
   14574:	2779                	jal	14d02 <h+0x1b2>
   14576:	28b2                	fld	fa7,264(sp)
   14578:	1cbc0eaf          	0x1cbc0eaf
   1457c:	2c61                	jal	14814 <GMb+0x4c4>
   1457e:	20f1                	jal	1464a <GMb+0x2fa>
   14580:	1925                	addi	s2,s2,-23
   14582:	0e44                	addi	s1,sp,788
   14584:	18c6                	slli	a7,a7,0x31
   14586:	2312                	fld	ft6,256(sp)
   14588:	08e0150f          	0x8e0150f
   1458c:	194c                	addi	a1,sp,180
   1458e:	1cf8                	addi	a4,sp,636
   14590:	20e2                	fld	ft1,24(sp)
   14592:	2a48                	fld	fa0,144(a2)
   14594:	2ed2                	fld	ft9,272(sp)
   14596:	1665                	addi	a2,a2,-7
   14598:	036c                	addi	a1,sp,396
   1459a:	1b76                	slli	s6,s6,0x3d
   1459c:	09840877          	0x9840877
   145a0:	0d72                	slli	s10,s10,0x1c
   145a2:	2401                	jal	147a2 <GMb+0x452>
   145a4:	200e                	fld	ft0,192(sp)
   145a6:	12fa                	slli	t0,t0,0x3e
   145a8:	174c                	addi	a1,sp,932
   145aa:	0aba                	slli	s5,s5,0xe
   145ac:	1c0a                	slli	s8,s8,0x22
   145ae:	059a                	slli	a1,a1,0x6
   145b0:	1cdd                	addi	s9,s9,-9
   145b2:	29a522af          	0x29a522af
   145b6:	2cc1                	jal	14886 <GMb+0x536>
   145b8:	107c                	addi	a5,sp,44
   145ba:	0598                	addi	a4,sp,704
   145bc:	2a50                	fld	fa2,144(a2)
   145be:	10e8                	addi	a0,sp,108
   145c0:	216d                	jal	14a6a <GMb+0x71a>
   145c2:	24ee074b          	0x24ee074b
   145c6:	0970                	addi	a2,sp,156
   145c8:	0ee8                	addi	a0,sp,860
   145ca:	2374                	fld	fa3,192(a4)
   145cc:	02ae                	slli	t0,t0,0xb
   145ce:	1511                	addi	a0,a0,-28
   145d0:	10f309db          	0x10f309db
   145d4:	026b17e3          	bne	s6,t1,14e02 <h+0x2b2>
   145d8:	03a9                	addi	t2,t2,10
   145da:	0b12                	slli	s6,s6,0x4
   145dc:	1e5f 0ccf 093b      	0x93b0ccf1e5f
   145e2:	1d40                	addi	s0,sp,692
   145e4:	17e0                	addi	s0,sp,1004
   145e6:	13c0                	addi	s0,sp,484
   145e8:	0338                	addi	a4,sp,392
   145ea:	27dc                	fld	fa5,136(a5)
   145ec:	2daa                	fld	fs11,136(sp)
   145ee:	0459                	addi	s0,s0,22
   145f0:	26780aa7          	0x26780aa7
   145f4:	0380                	addi	s0,sp,448
   145f6:	07ec                	addi	a1,sp,972
   145f8:	0a5e13d3          	fsub.d	ft7,ft8,ft5,rtz
   145fc:	28e0                	fld	fs0,208(s1)
   145fe:	1ecc                	addi	a1,sp,884
   14600:	2f89                	jal	14d52 <h+0x202>
   14602:	153a                	slli	a0,a0,0x2e
   14604:	0bfe                	slli	s7,s7,0x1f
   14606:	1900                	addi	s0,sp,176
   14608:	23ac                	fld	fa1,64(a5)
   1460a:	2d98                	fld	fa4,24(a1)
   1460c:	2f79                	jal	14daa <h+0x25a>
   1460e:	11a8                	addi	a0,sp,232
   14610:	04f9                	addi	s1,s1,30
   14612:	2ccc260b          	0x2ccc260b
   14616:	26d1                	jal	149da <GMb+0x68a>
   14618:	25f82737          	lui	a4,0x25f82
   1461c:	08d6                	slli	a7,a7,0x15
   1461e:	2bb824b7          	lui	s1,0x2bb82
   14622:	119f013b          	0x119f013b
   14626:	0486                	slli	s1,s1,0x1
   14628:	17ad                	addi	a5,a5,-21
   1462a:	1a5f 2e59 0165      	0x1652e591a5f
   14630:	11c61cc7          	fmsub.s	fs9,fa2,ft8,ft2,rtz
   14634:	215603d7          	0x215603d7
   14638:	20a0                	fld	fs0,64(s1)
   1463a:	278e                	fld	fa5,192(sp)
   1463c:	1d6a                	slli	s10,s10,0x3a
   1463e:	2425                	jal	14866 <GMb+0x516>
   14640:	1465110f          	0x1465110f
   14644:	0f9f 2249 0c59      	0xc5922490f9f
   1464a:	1b4e                	slli	s6,s6,0x33
   1464c:	1022                	c.slli	zero,0x28
   1464e:	2d84                	fld	fs1,24(a1)
   14650:	0d2e                	slli	s10,s10,0xb
   14652:	2cd5                	jal	14946 <GMb+0x5f6>
   14654:	06d9                	addi	a3,a3,22
   14656:	0124                	addi	s1,sp,136
   14658:	21e9                	jal	14b22 <GMb+0x7d2>
   1465a:	0af6                	slli	s5,s5,0x1d
   1465c:	288a                	fld	fa7,128(sp)
   1465e:	2f9c                	fld	fa5,24(a5)
   14660:	16a8                	addi	a0,sp,872
   14662:	0c6d2e23          	sw	t1,220(s10)
   14666:	07c4                	addi	s1,sp,964
   14668:	0400                	addi	s0,sp,512
   1466a:	247c                	fld	fa5,200(s0)
   1466c:	09ad                	addi	s3,s3,11
   1466e:	2ab0                	fld	fa2,80(a3)
   14670:	11e6                	slli	gp,gp,0x39
   14672:	1a5e                	slli	s4,s4,0x37
   14674:	157f0e23          	sb	s7,348(t5)
   14678:	1471                	addi	s0,s0,-4
   1467a:	099f 2116 1de2      	0x1de22116099f
   14680:	1f1c                	addi	a5,sp,944
   14682:	042f18fb          	0x42f18fb
   14686:	04f8                	addi	a4,sp,588
   14688:	0d92                	slli	s11,s11,0x4
   1468a:	2b25                	jal	14bc2 <h+0x72>
   1468c:	2c500cdb          	0x2c500cdb
   14690:	2136                	fld	ft2,328(sp)
   14692:	2506                	fld	fa0,64(sp)
   14694:	266d                	jal	14a3e <GMb+0x6ee>
   14696:	04e5                	addi	s1,s1,25
   14698:	0741                	addi	a4,a4,16
   1469a:	1859                	addi	a6,a6,-10
   1469c:	1270                	addi	a2,sp,300
   1469e:	2d29                	jal	14cb8 <h+0x168>
   146a0:	1792                	slli	a5,a5,0x24
   146a2:	2659                	jal	14a28 <GMb+0x6d8>
   146a4:	07050d0b          	0x7050d0b
   146a8:	18620b3f 08421450 	0x842145018620b3f
   146b0:	1f1a                	slli	t5,t5,0x26
   146b2:	2489                	jal	148f4 <GMb+0x5a4>
   146b4:	15632c63          	0x15632c63
   146b8:	17c4                	addi	s1,sp,996
   146ba:	2581                	jal	14cfa <h+0x1aa>
   146bc:	100c                	addi	a1,sp,32
   146be:	28c61c9b          	0x28c61c9b
   146c2:	24ff                	0x24ff
   146c4:	019804f7          	0x19804f7
   146c8:	1aff                	0x1aff
   146ca:	01680c07          	0x1680c07
   146ce:	2054                	fld	fa3,128(s0)
   146d0:	23c42d0f          	0x23c42d0f
   146d4:	2359                	jal	14c5a <h+0x10a>
   146d6:	03522d13          	slti	s10,tp,53
   146da:	21a9                	jal	14b24 <GMb+0x7d4>
   146dc:	0310                	addi	a2,sp,384
   146de:	208e1eef          	jal	t4,f58e6 <__BSS_END__+0xddce2>
   146e2:	2f8a                	fld	ft11,128(sp)
   146e4:	0736                	slli	a4,a4,0xd
   146e6:	27e5                	jal	14ece <h+0x37e>
   146e8:	2f98                	fld	fa4,24(a5)
   146ea:	2e7f1e93          	0x2e7f1e93
   146ee:	15e0                	addi	s0,sp,748
   146f0:	03f42633          	mulhsu	a2,s0,t6
   146f4:	02d1                	addi	t0,t0,20
   146f6:	0ae0                	addi	s0,sp,348
   146f8:	1a14                	addi	a3,sp,304
   146fa:	1998                	addi	a4,sp,240
   146fc:	14e4                	addi	s1,sp,620
   146fe:	1148                	addi	a0,sp,164
   14700:	1aa0                	addi	s0,sp,376
   14702:	20d5                	jal	147e6 <GMb+0x496>
   14704:	141e26e7          	0x141e26e7
   14708:	0934                	addi	a3,sp,152
   1470a:	15b0                	addi	a2,sp,744
   1470c:	05351493          	0x5351493
   14710:	2261                	jal	14898 <GMb+0x548>
   14712:	25bd                	jal	14d80 <h+0x230>
   14714:	1c8c                	addi	a1,sp,624
   14716:	169c                	addi	a5,sp,864
   14718:	132e                	slli	t1,t1,0x2b
   1471a:	038d                	addi	t2,t2,3
   1471c:	2d5d                	jal	14dd2 <h+0x282>
   1471e:	202e112b          	0x202e112b
   14722:	1a1e                	slli	s4,s4,0x27
   14724:	10ce                	slli	ra,ra,0x33
   14726:	0be4                	addi	s1,sp,476
   14728:	08ed                	addi	a7,a7,27
   1472a:	2fd9                	jal	14f00 <h+0x3b0>
   1472c:	240007ab          	0x240007ab
   14730:	10c8                	addi	a0,sp,100
   14732:	2e8e                	fld	ft9,192(sp)
   14734:	111302b7          	lui	t0,0x11130
   14738:	2641                	jal	14ab8 <GMb+0x768>
   1473a:	1314                	addi	a3,sp,416
   1473c:	27f6096b          	0x27f6096b
   14740:	0a5a                	slli	s4,s4,0x16
   14742:	0349                	addi	t1,t1,18
   14744:	0f32                	slli	t5,t5,0xc
   14746:	1c5027f7          	0x1c5027f7
   1474a:	2139                	jal	14b58 <h+0x8>
   1474c:	2bbc                	fld	fa5,80(a5)
   1474e:	1a20                	addi	s0,sp,312
   14750:	17ac0fdb          	0x17ac0fdb
   14754:	0e66                	slli	t3,t3,0x19
   14756:	1272                	slli	tp,tp,0x3c
   14758:	2e4d                	jal	14b0a <GMb+0x7ba>
   1475a:	16b8                	addi	a4,sp,872
   1475c:	1b92                	slli	s7,s7,0x24
   1475e:	1ad4                	addi	a3,sp,372
   14760:	2b81                	jal	14cb0 <h+0x160>
   14762:	1ef6                	slli	t4,t4,0x3d
   14764:	131e                	slli	t1,t1,0x27
   14766:	2ffc                	fld	fa5,216(a5)
   14768:	1006                	c.slli	zero,0x21
   1476a:	0f44                	addi	s1,sp,916
   1476c:	0e1a                	slli	t3,t3,0x6
   1476e:	197d                	addi	s2,s2,-1
   14770:	1f02                	slli	t5,t5,0x20
   14772:	1f2e                	slli	t5,t5,0x2b
   14774:	2ec9                	jal	14b46 <GMb+0x7f6>
   14776:	02191a63          	bne	s2,ra,147aa <GMb+0x45a>
   1477a:	11d2                	slli	gp,gp,0x34
   1477c:	20230657          	0x20230657
   14780:	2cbd                	jal	149fe <GMb+0x6ae>
   14782:	1d78                	addi	a4,sp,700
   14784:	038a                	slli	t2,t2,0x2
   14786:	2e28                	fld	fa0,88(a2)
   14788:	254c                	fld	fa1,136(a0)
   1478a:	2a6a                	fld	fs4,152(sp)
   1478c:	0aff25e7          	0xaff25e7
   14790:	2dd8                	fld	fa4,152(a1)
   14792:	1a9d                	addi	s5,s5,-25
   14794:	03331b43          	fmadd.d	fs6,ft6,fs3,ft0,rtz
   14798:	187f22c7          	fmsub.s	ft5,ft10,ft7,ft3,rdn
   1479c:	015c2a5b          	0x15c2a5b
   147a0:	1d5a                	slli	s10,s10,0x36
   147a2:	19272093          	slti	ra,a4,402
   147a6:	02b6                	slli	t0,t0,0xd
   147a8:	0354                	addi	a3,sp,388
   147aa:	0add161b          	0xadd161b
   147ae:	0e84                	addi	s1,sp,848
   147b0:	2d45                	jal	14e60 <h+0x310>
   147b2:	0bd0                	addi	a2,sp,468
   147b4:	21d305f3          	0x21d305f3
   147b8:	1012                	c.slli	zero,0x24
   147ba:	29f2                	fld	fs3,280(sp)
   147bc:	16fd0ce7          	jalr	s9,367(s10)
   147c0:	0ba2                	slli	s7,s7,0x8
   147c2:	1c79                	addi	s8,s8,-2
   147c4:	2e6c                	fld	fa1,216(a2)
   147c6:	246b23a3          	sw	t1,583(s6)
   147ca:	2e36                	fld	ft8,328(sp)
   147cc:	0062                	c.slli	zero,0x18
   147ce:	09de                	slli	s3,s3,0x17
   147d0:	0844                	addi	s1,sp,20
   147d2:	2c8f1023          	sh	s0,704(t5)
   147d6:	0734                	addi	a3,sp,904
   147d8:	0e3d                	addi	t3,t3,15
   147da:	0f4c                	addi	a1,sp,916
   147dc:	1fc5                	addi	t6,t6,-15
   147de:	08b0                	addi	a2,sp,88
   147e0:	1f9c2a77          	0x1f9c2a77
   147e4:	176525b3          	0x176525b3
   147e8:	1be4                	addi	s1,sp,508
   147ea:	2120                	fld	fs0,64(a0)
   147ec:	0686                	slli	a3,a3,0x1
   147ee:	009f 2aab 1336      	0x13362aab009f
   147f4:	0080                	addi	s0,sp,64
   147f6:	1c90                	addi	a2,sp,624
   147f8:	02d5                	addi	t0,t0,21
   147fa:	23c5                	jal	14dda <h+0x28a>
   147fc:	138e                	slli	t2,t2,0x23
   147fe:	18f9                	addi	a7,a7,-2
   14800:	0da6                	slli	s11,s11,0x9
   14802:	2adc179b          	0x2adc179b
   14806:	1825                	addi	a6,a6,-23
   14808:	2e3e                	fld	ft8,456(sp)
   1480a:	0d5f 2912 1df4      	0x1df429120d5f
   14810:	0e6d                	addi	t3,t3,27
   14812:	1a02                	slli	s4,s4,0x20
   14814:	1af9                	addi	s5,s5,-2
   14816:	2eb1                	jal	14b72 <h+0x22>
   14818:	27e4                	fld	fs1,200(a5)
   1481a:	2e92                	fld	ft9,256(sp)
   1481c:	238d                	jal	14d7e <h+0x22e>
   1481e:	20ad                	jal	14888 <GMb+0x538>
   14820:	13f6                	slli	t2,t2,0x3d
   14822:	002d                	c.nop	11
   14824:	0960                	addi	s0,sp,156
   14826:	0781                	addi	a5,a5,0
   14828:	1119                	addi	sp,sp,-26
   1482a:	0aa0                	addi	s0,sp,344
   1482c:	069f 0033 0af8      	0xaf80033069f
   14832:	028a                	slli	t0,t0,0x2
   14834:	0768                	addi	a0,sp,908
   14836:	270d                	jal	14f58 <h+0x408>
   14838:	2ecc26f3          	csrrs	a3,0x2ec,s8
   1483c:	1fa2                	slli	t6,t6,0x28
   1483e:	12e1                	addi	t0,t0,-8
   14840:	10a11027          	0x10a11027
   14844:	16ce                	slli	a3,a3,0x33
   14846:	129d                	addi	t0,t0,-25
   14848:	2ae9                	jal	14a22 <GMb+0x6d2>
   1484a:	2d0c                	fld	fa1,24(a0)
   1484c:	024e                	slli	tp,tp,0x13
   1484e:	2fa6                	fld	ft11,72(sp)
   14850:	01e2                	slli	gp,gp,0x18
   14852:	2f8d                	jal	14fc4 <h+0x474>
   14854:	07d6                	slli	a5,a5,0x15
   14856:	1b98                	addi	a4,sp,496
   14858:	2722                	fld	fa4,8(sp)
   1485a:	0f48                	addi	a0,sp,916
   1485c:	2ef0                	fld	fa2,216(a3)
   1485e:	2c622917          	auipc	s2,0x2c622
   14862:	1b2a                	slli	s6,s6,0x2a
   14864:	08a2                	slli	a7,a7,0x8
   14866:	011c                	addi	a5,sp,128
   14868:	1525                	addi	a0,a0,-23
   1486a:	19c9                	addi	s3,s3,-14
   1486c:	0f19                	addi	t5,t5,6
   1486e:	2bb42863          	0x2bb42863
   14872:	02051857          	0x2051857
   14876:	255c                	fld	fa5,136(a0)
   14878:	2c11                	jal	14a8c <GMb+0x73c>
   1487a:	04ba0f17          	auipc	t5,0x4ba0
   1487e:	11fc                	addi	a5,sp,236
   14880:	1fe0                	addi	s0,sp,1020
   14882:	00992cb7          	lui	s9,0x992
   14886:	1c24                	addi	s1,sp,568
   14888:	13e11683          	lh	a3,318(sp) # 19d45332 <__BSS_END__+0x19d2d72e>
   1488c:	2420                	fld	fs0,72(s0)
   1488e:	2f7a                	fld	ft10,408(sp)
   14890:	2de4                	fld	fs1,216(a1)
   14892:	054a                	slli	a0,a0,0x12
   14894:	1a10                	addi	a2,sp,304
   14896:	159c00b3          	0x159c00b3
   1489a:	0a56                	slli	s4,s4,0x15
   1489c:	1735                	addi	a4,a4,-19
   1489e:	2f99                	jal	14ff4 <h+0x4a4>
   148a0:	035e                	slli	t1,t1,0x17
   148a2:	0c56                	slli	s8,s8,0x15
   148a4:	01dd                	addi	gp,gp,23
   148a6:	162e1c6f          	jal	s8,f5a08 <__BSS_END__+0xdde04>
   148aa:	1eea                	slli	t4,t4,0x3a
   148ac:	109e                	slli	ra,ra,0x27
   148ae:	012e                	slli	sp,sp,0xb
   148b0:	0b4d                	addi	s6,s6,19
   148b2:	2782                	fld	fa5,0(sp)
   148b4:	1aea                	slli	s5,s5,0x3a
   148b6:	2558                	fld	fa4,136(a0)
   148b8:	2e8125af          	0x2e8125af
   148bc:	1002                	c.slli	zero,0x20
   148be:	2660                	fld	fs0,200(a2)
   148c0:	281d                	jal	148f6 <GMb+0x5a6>
   148c2:	0549                	addi	a0,a0,18
   148c4:	14cd29db          	0x14cd29db
   148c8:	186e                	slli	a6,a6,0x3b
   148ca:	070f0f6f          	jal	t5,10493a <__BSS_END__+0xecd36>
   148ce:	1931                	addi	s2,s2,-20
   148d0:	051c1427          	0x51c1427
   148d4:	0d4c207b          	0xd4c207b
   148d8:	0755                	addi	a4,a4,21
   148da:	007004cf          	fnmadd.s	fs1,ft0,ft7,ft0,rne
   148de:	18fe                	slli	a7,a7,0x3f
   148e0:	2dcc                	fld	fa1,152(a1)
   148e2:	2ff0                	fld	fa2,216(a5)
   148e4:	1c76                	slli	s8,s8,0x3d
   148e6:	2ff205b3          	0x2ff205b3
   148ea:	26a8                	fld	fa0,72(a3)
   148ec:	0d80                	addi	s0,sp,720
   148ee:	0320                	addi	s0,sp,392
   148f0:	0575                	addi	a0,a0,29
   148f2:	29b6                	fld	fs3,328(sp)
   148f4:	1cfc0067          	jr	463(s8)
   148f8:	1f28                	addi	a0,sp,952
   148fa:	03a8                	addi	a0,sp,456
   148fc:	02fc                	addi	a5,sp,332
   148fe:	0278                	addi	a4,sp,268
   14900:	1f3c                	addi	a5,sp,952
   14902:	201f 20fd 1e4e      	0x1e4e20fd201f
   14908:	2a76                	fld	fs4,344(sp)
   1490a:	09cc2563          	0x9cc2563
   1490e:	079a                	slli	a5,a5,0x6
   14910:	197c                	addi	a5,sp,188
   14912:	27ae                	fld	fa5,200(sp)
   14914:	0414                	addi	a3,sp,512
   14916:	10f2                	slli	ra,ra,0x3c
   14918:	0999                	addi	s3,s3,6
   1491a:	0e39                	addi	t3,t3,14
   1491c:	102b067b          	0x102b067b
   14920:	1250                	addi	a2,sp,292
   14922:	2605                	jal	14c42 <h+0xf2>
   14924:	2b8c                	fld	fa1,16(a5)
   14926:	0f6a                	slli	t5,t5,0x1a
   14928:	0822                	slli	a6,a6,0x8
   1492a:	148d                	addi	s1,s1,-29
   1492c:	07f4                	addi	a3,sp,972
   1492e:	2e4a                	fld	ft8,144(sp)
   14930:	1dd4                	addi	a3,sp,756
   14932:	2fcc                	fld	fa1,152(a5)
   14934:	14f6                	slli	s1,s1,0x3d
   14936:	094c                	addi	a1,sp,148
   14938:	1e280577          	0x1e280577
   1493c:	0834                	addi	a3,sp,24
   1493e:	0c91                	addi	s9,s9,4
   14940:	2aa0                	fld	fs0,80(a3)
   14942:	22c2                	fld	ft5,16(sp)
   14944:	1d9a                	slli	s11,s11,0x26
   14946:	0ae72edb          	0xae72edb
   1494a:	0d1b04bf 08db0a97 	0x8db0a970d1b04bf
   14952:	07d4                	addi	a3,sp,964
   14954:	2178                	fld	fa4,192(a0)
   14956:	27c0                	fld	fs0,136(a5)
   14958:	0c8e                	slli	s9,s9,0x3
   1495a:	0921                	addi	s2,s2,8
   1495c:	06d6                	slli	a3,a3,0x15
   1495e:	1279                	addi	tp,tp,-2
   14960:	1385                	addi	t2,t2,-31
   14962:	18ab1cf7          	0x18ab1cf7
   14966:	2f0c                	fld	fa1,24(a4)
   14968:	1116                	slli	sp,sp,0x25
   1496a:	1bf5                	addi	s7,s7,-3
   1496c:	12ec                	addi	a1,sp,364
   1496e:	1f4300d3          	fdiv.q	ft1,ft6,fs4,rne
   14972:	244a27af          	amoxor.w.aq	a5,tp,(s4)
   14976:	2cd9                	jal	14c4c <h+0xfc>
   14978:	092006c7          	fmsub.s	fa3,ft0,fs2,ft1,rne
   1497c:	16a1                	addi	a3,a3,-24
   1497e:	20002693          	slti	a3,zero,512
   14982:	03da                	slli	t2,t2,0x16
   14984:	05791d67          	0x5791d67
   14988:	0366                	slli	t1,t1,0x19
   1498a:	0e1f 2111 0ac4      	0xac421110e1f
   14990:	262a                	fld	fa2,136(sp)
   14992:	07f2                	slli	a5,a5,0x1c
   14994:	27b8                	fld	fa4,72(a5)
   14996:	0cc0                	addi	s0,sp,596
   14998:	17f4                	addi	a3,sp,1004
   1499a:	0036                	c.slli	zero,0xd
   1499c:	0b40                	addi	s0,sp,404
   1499e:	2e1d129b          	0x2e1d129b
   149a2:	0c02                	c.slli64	s8
   149a4:	205e                	fld	ft0,464(sp)
   149a6:	24d4                	fld	fa3,136(s1)
   149a8:	1311                	addi	t1,t1,-28
   149aa:	1b15                	addi	s6,s6,-27
   149ac:	0442                	slli	s0,s0,0x10
   149ae:	2736                	fld	fa4,328(sp)
   149b0:	02c40a07          	0x2c40a07
   149b4:	037d                	addi	t1,t1,31
   149b6:	1941                	addi	s2,s2,-16
   149b8:	1362                	slli	t1,t1,0x38
   149ba:	2728                	fld	fa0,72(a4)
   149bc:	082a                	slli	a6,a6,0xa
   149be:	1656                	slli	a2,a2,0x35
   149c0:	030c29f7          	0x30c29f7
   149c4:	127d                	addi	tp,tp,-1
   149c6:	0856120f          	0x856120f
   149ca:	12c20827          	0x12c20827
   149ce:	0374                	addi	a3,sp,396
   149d0:	14fc                	addi	a5,sp,620
   149d2:	173216a3          	sh	s3,365(tp) # 16d <main-0xff07>
   149d6:	10ed                	addi	ra,ra,-5
   149d8:	199f 1d7d 1495      	0x14951d7d199f
   149de:	29a8                	fld	fa0,80(a1)
   149e0:	109c                	addi	a5,sp,96
   149e2:	0cbc                	addi	a5,sp,600
   149e4:	171d                	addi	a4,a4,-25
   149e6:	2a3e                	fld	fs4,456(sp)
   149e8:	1688                	addi	a0,sp,864
   149ea:	26ff                	0x26ff
   149ec:	1fa0                	addi	s0,sp,1016
   149ee:	1a901e6f          	jal	t3,16396 <hm+0x846>
   149f2:	18801d43          	fmadd.s	fs10,ft0,fs0,ft3,rtz
   149f6:	2ac30773          	0x2ac30773
   149fa:	1891                	addi	a7,a7,-28
   149fc:	17902e1b          	0x17902e1b
   14a00:	2cb9                	jal	14c5e <h+0x10e>
   14a02:	23f10493          	addi	s1,sp,575
   14a06:	1efd                	addi	t4,t4,-1
   14a08:	1f2209af          	0x1f2209af
   14a0c:	2c49                	jal	14c9e <h+0x14e>
   14a0e:	1b96                	slli	s7,s7,0x25
   14a10:	1a4822cf          	fnmadd.d	ft5,fa6,ft4,ft3,rdn
   14a14:	198e                	slli	s3,s3,0x23
   14a16:	1fb2                	slli	t6,t6,0x2c
   14a18:	227c                	fld	fa5,192(a2)
   14a1a:	0dd919c3          	0xdd919c3
   14a1e:	10fc                	addi	a5,sp,108
   14a20:	1202                	slli	tp,tp,0x20
   14a22:	089d                	addi	a7,a7,7
   14a24:	1faa1b57          	0x1faa1b57
   14a28:	15b8                	addi	a4,sp,744
   14a2a:	2896                	fld	fa7,320(sp)
   14a2c:	2469                	jal	14cb6 <h+0x166>
   14a2e:	096d09c3          	fmadd.s	fs3,fs10,fs6,ft1,rne
   14a32:	1c68                	addi	a0,sp,572
   14a34:	1ae1                	addi	s5,s5,-8
   14a36:	2956                	fld	fs2,336(sp)
   14a38:	245c                	fld	fa5,136(s0)
   14a3a:	24dd                	jal	14d20 <h+0x1d0>
   14a3c:	0de2                	slli	s11,s11,0x18
   14a3e:	0cfe                	slli	s9,s9,0x1f
   14a40:	2ec11767          	0x2ec11767
   14a44:	2ffb0d57          	0x2ffb0d57
   14a48:	266e                	fld	fa2,216(sp)
   14a4a:	2f1f 10ec 1e96      	0x1e9610ec2f1f
   14a50:	2c41                	jal	14ce0 <h+0x190>
   14a52:	19cd                	addi	s3,s3,-13
   14a54:	07fc2fef          	jal	t6,d72d2 <__BSS_END__+0xbf6ce>
   14a58:	1cb92d5b          	0x1cb92d5b
   14a5c:	2bc1                	jal	1502c <h+0x4dc>
   14a5e:	2d3e                	fld	fs10,456(sp)
   14a60:	0e95                	addi	t4,t4,5
   14a62:	26fa22ef          	jal	t0,b74d0 <__BSS_END__+0x9f8cc>
   14a66:	1c00065b          	0x1c00065b
   14a6a:	0f5f 13ba 0aca      	0xaca13ba0f5f
   14a70:	1d48                	addi	a0,sp,692
   14a72:	02f3288f          	0x2f3288f
   14a76:	0676                	slli	a2,a2,0x1d
   14a78:	2f15                	jal	151ac <h+0x65c>
   14a7a:	1358                	addi	a4,sp,420
   14a7c:	2796                	fld	fa5,320(sp)
   14a7e:	112a                	slli	sp,sp,0x2a
   14a80:	19c0                	addi	s0,sp,244
   14a82:	1eda                	slli	t4,t4,0x36
   14a84:	1d49                	addi	s10,s10,-14
   14a86:	22c8                	fld	fa0,128(a3)
   14a88:	2efd                	jal	14e86 <h+0x336>
   14a8a:	0dfd                	addi	s11,s11,31
   14a8c:	29fc                	fld	fa5,208(a1)
   14a8e:	162a                	slli	a2,a2,0x2a
   14a90:	2876                	fld	fa6,344(sp)
   14a92:	1325                	addi	t1,t1,-23
   14a94:	1cf6                	slli	s9,s9,0x3d
   14a96:	02c62243          	fmadd.d	ft4,fa2,fa2,ft0,rdn
   14a9a:	1a6c                	addi	a1,sp,316
   14a9c:	210e                	fld	ft2,192(sp)
   14a9e:	1c19                	addi	s8,s8,-26
   14aa0:	1c6a14fb          	0x1c6a14fb
   14aa4:	2b4c                	fld	fa1,144(a4)
   14aa6:	0122                	slli	sp,sp,0x8
   14aa8:	1eb8                	addi	a4,sp,888
   14aaa:	2e2e1aab          	0x2e2e1aab
   14aae:	09cd                	addi	s3,s3,19
   14ab0:	19b2                	slli	s3,s3,0x2c
   14ab2:	0fba                	slli	t6,t6,0xe
   14ab4:	05b216af          	0x5b216af
   14ab8:	1659                	addi	a2,a2,-10
   14aba:	1682                	slli	a3,a3,0x20
   14abc:	1052                	c.slli	zero,0x34
   14abe:	0839                	addi	a6,a6,14
   14ac0:	2d65                	jal	15178 <h+0x628>
   14ac2:	12f4                	addi	a3,sp,364
   14ac4:	22c1                	jal	14c84 <h+0x134>
   14ac6:	0b28                	addi	a0,sp,408
   14ac8:	2cf6                	fld	fs9,344(sp)
   14aca:	2430                	fld	fa2,72(s0)
   14acc:	09d8                	addi	a4,sp,212
   14ace:	2248                	fld	fa0,128(a2)
   14ad0:	0a571b63          	bne	a4,t0,14b86 <h+0x36>
   14ad4:	076a                	slli	a4,a4,0x1a
   14ad6:	1b7f                	0x1b7f
   14ad8:	173e                	slli	a4,a4,0x2f
   14ada:	15702b9b          	0x15702b9b
   14ade:	1885                	addi	a7,a7,-31
   14ae0:	23de                	fld	ft7,464(sp)
   14ae2:	2cc0                	fld	fs0,152(s1)
   14ae4:	0279                	addi	tp,tp,30
   14ae6:	273e                	fld	fa4,456(sp)
   14ae8:	2d22                	fld	fs10,8(sp)
   14aea:	1601                	addi	a2,a2,-32
   14aec:	091d2573          	csrrs	a0,0x91,s10
   14af0:	1b60                	addi	s0,sp,444
   14af2:	1bac                	addi	a1,sp,504
   14af4:	1c1f13b7          	lui	t2,0x1c1f1
   14af8:	2689                	jal	14e3a <h+0x2ea>
   14afa:	2325                	jal	15022 <h+0x4d2>
   14afc:	0239                	addi	tp,tp,14
   14afe:	18f6                	slli	a7,a7,0x3d
   14b00:	2a5d                	jal	14cb6 <h+0x166>
   14b02:	204c25cf          	fnmadd.s	fa1,fs8,ft4,ft4,rdn
   14b06:	2cd0                	fld	fa2,152(s1)
   14b08:	07cd106b          	0x7cd106b
   14b0c:	0002                	c.slli64	zero
   14b0e:	00a22473          	csrrs	s0,0xa,tp
   14b12:	1826                	slli	a6,a6,0x29
   14b14:	07d0                	addi	a2,sp,964
   14b16:	0e41                	addi	t3,t3,16
   14b18:	2640                	fld	fs0,136(a2)
   14b1a:	1d8518db          	0x1d8518db
   14b1e:	213e182b          	0x213e182b
   14b22:	15a026cf          	0x15a026cf
   14b26:	0e7a233b          	0xe7a233b
   14b2a:	2ee9                	jal	14f04 <h+0x3b4>
   14b2c:	05ac                	addi	a1,sp,712
   14b2e:	15760bfb          	0x15760bfb
   14b32:	25dc                	fld	fa5,136(a1)
   14b34:	1301                	addi	t1,t1,-32
   14b36:	1bc21783          	lh	a5,444(tp) # 1bc <main-0xfeb8>
   14b3a:	258a                	fld	fa1,128(sp)
   14b3c:	11ec                	addi	a1,sp,236
   14b3e:	27b5                	jal	152aa <h+0x75a>
   14b40:	1875                	addi	a6,a6,-3
   14b42:	16ff                	0x16ff
   14b44:	0a5c                	addi	a5,sp,276
   14b46:	27bc                	fld	fa5,72(a5)
   14b48:	062c                	addi	a1,sp,776
   14b4a:	121e288b          	0x121e288b
   14b4e:	26dd                	jal	14f34 <h+0x3e4>

00014b50 <h>:
   14b50:	2db0                	fld	fa2,88(a1)
   14b52:	24cf2767          	0x24cf2767
   14b56:	1ef2200f          	0x1ef2200f
   14b5a:	0059                	c.nop	22
   14b5c:	148f0d3f 07640bb2 	0x7640bb2148f0d3f
   14b64:	0754                	addi	a3,sp,900
   14b66:	2a74                	fld	fa3,208(a2)
   14b68:	251a                	fld	fa0,384(sp)
   14b6a:	2532                	fld	fa0,264(sp)
   14b6c:	0edc09e7          	jalr	s3,237(s8)
   14b70:	14c8                	addi	a0,sp,612
   14b72:	0d70                	addi	a2,sp,668
   14b74:	0405                	addi	s0,s0,1
   14b76:	2ba9                	jal	150d0 <h+0x580>
   14b78:	14f9                	addi	s1,s1,-2
   14b7a:	11d2                	slli	gp,gp,0x34
   14b7c:	2596                	fld	fa1,320(sp)
   14b7e:	27d8                	fld	fa4,136(a5)
   14b80:	2470                	fld	fa2,200(s0)
   14b82:	2e0a                	fld	ft8,128(sp)
   14b84:	1b28                	addi	a0,sp,440
   14b86:	0059                	c.nop	22
   14b88:	2b1e2ac7          	fmsub.d	fs5,ft8,fa7,ft5,rdn
   14b8c:	162a                	slli	a2,a2,0x2a
   14b8e:	2b2e                	fld	fs6,200(sp)
   14b90:	0212                	slli	tp,tp,0x4
   14b92:	239e                	fld	ft7,448(sp)
   14b94:	20da09d7          	0x20da09d7
   14b98:	1a15                	addi	s4,s4,-27
   14b9a:	19ab07eb          	0x19ab07eb
   14b9e:	0561                	addi	a0,a0,24
   14ba0:	2b5e2a63          	0x2b5e2a63
   14ba4:	2f78                	fld	fa4,216(a4)
   14ba6:	0f4a                	slli	t5,t5,0x12
   14ba8:	0c4a                	slli	s8,s8,0x12
   14baa:	2442                	fld	fs0,16(sp)
   14bac:	0f1e                	slli	t5,t5,0x7
   14bae:	1d42                	slli	s10,s10,0x30
   14bb0:	1749                	addi	a4,a4,-14
   14bb2:	0a56                	slli	s4,s4,0x15
   14bb4:	07cc                	addi	a1,sp,964
   14bb6:	1eaa                	slli	t4,t4,0x2a
   14bb8:	1dad                	addi	s11,s11,-21
   14bba:	28b4                	fld	fa3,80(s1)
   14bbc:	1482                	slli	s1,s1,0x20
   14bbe:	2734                	fld	fa3,72(a4)
   14bc0:	0044                	addi	s1,sp,4
   14bc2:	26bc                	fld	fa5,72(a3)
   14bc4:	0d1a                	slli	s10,s10,0x6
   14bc6:	2b1d                	jal	150fc <h+0x5ac>
   14bc8:	081f 1653 085c      	0x85c1653081f
   14bce:	272329bf 178c0e47 	0x178c0e47272329bf
   14bd6:	28b101a3          	sb	a1,643(sp)
   14bda:	285e0d2f          	0x285e0d2f
   14bde:	0e7f16e3          	bne	t5,t2,154ca <sig+0x17a>
   14be2:	1506                	slli	a0,a0,0x21
   14be4:	2295                	jal	14d48 <h+0x1f8>
   14be6:	2c4c                	fld	fa1,152(s0)
   14be8:	2a24                	fld	fs1,80(a2)
   14bea:	2e02080f          	0x2e02080f
   14bee:	11c92957          	0x11c92957
   14bf2:	03c8                	addi	a0,sp,452
   14bf4:	2275                	jal	14da0 <h+0x250>
   14bf6:	1898                	addi	a4,sp,112
   14bf8:	048c0897          	auipc	a7,0x48c0
   14bfc:	1d18                	addi	a4,sp,688
   14bfe:	1d84                	addi	s1,sp,752
   14c00:	0fcd                	addi	t6,t6,19
   14c02:	185603b7          	lui	t2,0x18560
   14c06:	06c22af3          	csrrs	s5,0x6c,tp
   14c0a:	04700e63          	beq	zero,t2,14c66 <h+0x116>
   14c0e:	2338                	fld	fa4,64(a4)
   14c10:	215e                	fld	ft2,464(sp)
   14c12:	06e8                	addi	a0,sp,844
   14c14:	28ce                	fld	fa7,208(sp)
   14c16:	02df 1e7c 21f9      	0x21f91e7c02df
   14c1c:	11b9                	addi	gp,gp,-18
   14c1e:	2224                	fld	fs1,64(a2)
   14c20:	2051                	jal	14ca4 <h+0x154>
   14c22:	22c407e7          	jalr	a5,556(s0) # 1922c <__BSS_END__+0x1628>
   14c26:	126d                	addi	tp,tp,-5
   14c28:	2205                	jal	14d48 <h+0x1f8>
   14c2a:	2e65                	jal	14fe2 <h+0x492>
   14c2c:	0dec                	addi	a1,sp,732
   14c2e:	17d6                	slli	a5,a5,0x35
   14c30:	1b5a                	slli	s6,s6,0x36
   14c32:	185a                	slli	a6,a6,0x36
   14c34:	18aa                	slli	a7,a7,0x2a
   14c36:	0c9d                	addi	s9,s9,7
   14c38:	08fc                	addi	a5,sp,92
   14c3a:	1015                	c.nop	-27
   14c3c:	2e8a                	fld	ft9,128(sp)
   14c3e:	03bc1af3          	csrrw	s5,0x3b,s8
   14c42:	1afc0a0f          	0x1afc0a0f
   14c46:	2b95                	jal	151ba <h+0x66a>
   14c48:	2538                	fld	fa4,72(a0)
   14c4a:	0462                	slli	s0,s0,0x18
   14c4c:	1453038f          	0x1453038f
   14c50:	1cfc12fb          	0x1cfc12fb
   14c54:	03d2                	slli	t2,t2,0x14
   14c56:	0aad                	addi	s5,s5,11
   14c58:	0be1                	addi	s7,s7,24
   14c5a:	1e94                	addi	a3,sp,880
   14c5c:	25881763          	bne	a6,s8,14eaa <h+0x35a>
   14c60:	096c                	addi	a1,sp,156
   14c62:	0ffc                	addi	a5,sp,988
   14c64:	257a                	fld	fa0,408(sp)
   14c66:	066d                	addi	a2,a2,27
   14c68:	1dda01cf          	0x1dda01cf
   14c6c:	2b1e                	fld	fs6,448(sp)
   14c6e:	101d                	c.nop	-25
   14c70:	0728                	addi	a0,sp,904
   14c72:	2da2                	fld	fs11,8(sp)
   14c74:	1cbe                	slli	s9,s9,0x2f
   14c76:	2ab82423          	sw	a1,680(a6)
   14c7a:	21da                	fld	ft3,400(sp)
   14c7c:	26b9                	jal	14fca <h+0x47a>
   14c7e:	07ed                	addi	a5,a5,27
   14c80:	0ab8                	addi	a4,sp,344
   14c82:	141d                	addi	s0,s0,-25
   14c84:	0fee                	slli	t6,t6,0x1b
   14c86:	062c                	addi	a1,sp,776
   14c88:	15d2                	slli	a1,a1,0x34
   14c8a:	24a2                	fld	fs1,8(sp)
   14c8c:	049d                	addi	s1,s1,7
   14c8e:	0ece                	slli	t4,t4,0x13
   14c90:	116e                	slli	sp,sp,0x3b
   14c92:	04b607a7          	0x4b607a7
   14c96:	116d                	addi	sp,sp,-5
   14c98:	031f 0367 12cf      	0x12cf0367031f
   14c9e:	29e6                	fld	fs3,88(sp)
   14ca0:	2e14                	fld	fa3,24(a2)
   14ca2:	107e                	c.slli	zero,0x3f
   14ca4:	2134                	fld	fa3,64(a0)
   14ca6:	018e                	slli	gp,gp,0x3
   14ca8:	05b9                	addi	a1,a1,14
   14caa:	1358                	addi	a4,sp,420
   14cac:	26cc                	fld	fa1,136(a3)
   14cae:	078d220f          	0x78d220f
   14cb2:	1950                	addi	a2,sp,180
   14cb4:	2612                	fld	fa2,256(sp)
   14cb6:	041f 116b 2b41      	0x2b41116b041f
   14cbc:	1e30                	addi	a2,sp,824
   14cbe:	22f4                	fld	fa3,192(a3)
   14cc0:	0898                	addi	a4,sp,80
   14cc2:	261c                	fld	fa5,8(a2)
   14cc4:	11371a3b          	0x11371a3b
   14cc8:	1e5d0b67          	jalr	s6,485(s10)
   14ccc:	2ad1                	jal	14ea0 <h+0x350>
   14cce:	0dcc                	addi	a1,sp,724
   14cd0:	23b4                	fld	fa3,64(a5)
   14cd2:	0079                	c.nop	30
   14cd4:	2901                	jal	150e4 <h+0x594>
   14cd6:	2951                	jal	1516a <h+0x61a>
   14cd8:	1ee8                	addi	a0,sp,892
   14cda:	293a                	fld	fs2,392(sp)
   14cdc:	11a0                	addi	s0,sp,232
   14cde:	1ac0                	addi	s0,sp,372
   14ce0:	21c2                	fld	ft3,16(sp)
   14ce2:	2bcc                	fld	fa1,144(a5)
   14ce4:	20e1                	jal	14dac <h+0x25c>
   14ce6:	2cde29c3          	0x2cde29c3
   14cea:	0bc6                	slli	s7,s7,0x11
   14cec:	2195                	jal	15150 <h+0x600>
   14cee:	2ce9                	jal	14fc8 <h+0x478>
   14cf0:	21b5                	jal	1515c <h+0x60c>
   14cf2:	00cd                	addi	ra,ra,19
   14cf4:	1d26                	slli	s10,s10,0x29
   14cf6:	0c80                	addi	s0,sp,592
   14cf8:	1c79                	addi	s8,s8,-2
   14cfa:	2e78066b          	0x2e78066b
   14cfe:	0c94                	addi	a3,sp,592
   14d00:	2874                	fld	fa3,208(s0)
   14d02:	1321                	addi	t1,t1,-24
   14d04:	10f70bd7          	0x10f70bd7
   14d08:	1d65                	addi	s10,s10,-7
   14d0a:	2db6                	fld	fs11,328(sp)
   14d0c:	2e58                	fld	fa4,152(a2)
   14d0e:	0bd016ab          	0xbd016ab
   14d12:	2acd                	jal	14f04 <h+0x3b4>
   14d14:	22c4                	fld	fs1,128(a3)
   14d16:	0f51                	addi	t5,t5,20
   14d18:	2ce8                	fld	fa0,216(s1)
   14d1a:	1e5f2d1b          	0x1e5f2d1b
   14d1e:	01fa                	slli	gp,gp,0x1e
   14d20:	29010be7          	jalr	s7,656(sp)
   14d24:	1051                	c.nop	-12
   14d26:	0d0e                	slli	s10,s10,0x3
   14d28:	2d20282f          	0x2d20282f
   14d2c:	1342                	slli	t1,t1,0x30
   14d2e:	2a49                	jal	14ec0 <h+0x370>
   14d30:	1aa2                	slli	s5,s5,0x28
   14d32:	2fd5                	jal	15526 <sig+0x1d6>
   14d34:	1db2                	slli	s11,s11,0x2c
   14d36:	1f34                	addi	a3,sp,952
   14d38:	2a51098b          	0x2a51098b
   14d3c:	20cc                	fld	fa1,128(s1)
   14d3e:	238b1977          	0x238b1977
   14d42:	06fc14b7          	lui	s1,0x6fc1
   14d46:	16702fcf          	fnmadd.q	ft11,ft0,ft7,ft2,rdn
   14d4a:	07c0                	addi	s0,sp,964
   14d4c:	2600                	fld	fs0,8(a2)
   14d4e:	100c18a7          	0x100c18a7
   14d52:	168625cb          	fnmsub.q	fa1,fa2,fs0,ft2,rdn
   14d56:	2465                	jal	14ffe <h+0x4ae>
   14d58:	23ba2f17          	auipc	t5,0x23ba2
   14d5c:	2d5f 208c 1e0b      	0x1e0b208c2d5f
   14d62:	1e40                	addi	s0,sp,820
   14d64:	04df 0843 17c5      	0x17c5084304df
   14d6a:	1fdd                	addi	t6,t6,-9
   14d6c:	2dbc                	fld	fa5,88(a1)
   14d6e:	1f88                	addi	a0,sp,1008
   14d70:	029d                	addi	t0,t0,7
   14d72:	0311                	addi	t1,t1,4
   14d74:	1e45                	addi	t3,t3,-15
   14d76:	0701                	addi	a4,a4,0
   14d78:	1751                	addi	a4,a4,-12
   14d7a:	11ac                	addi	a1,sp,232
   14d7c:	2f35                	jal	154b8 <sig+0x168>
   14d7e:	236c                	fld	fa1,192(a4)
   14d80:	042a                	slli	s0,s0,0xa
   14d82:	14f50543          	0x14f50543
   14d86:	2120                	fld	fs0,64(a0)
   14d88:	1ad2                	slli	s5,s5,0x34
   14d8a:	0239                	addi	tp,tp,14
   14d8c:	0009                	c.nop	2
   14d8e:	1ab4                	addi	a3,sp,376
   14d90:	1202                	slli	tp,tp,0x20
   14d92:	135a198f          	0x135a198f
   14d96:	1081                	addi	ra,ra,-32
   14d98:	21fc                	fld	fa5,192(a1)
   14d9a:	0979                	addi	s2,s2,30
   14d9c:	2e95                	jal	15110 <h+0x5c0>
   14d9e:	239a                	fld	ft7,384(sp)
   14da0:	0888                	addi	a0,sp,80
   14da2:	20e42c07          	flw	fs8,526(s0)
   14da6:	012a                	slli	sp,sp,0xa
   14da8:	0d65                	addi	s10,s10,25
   14daa:	0551                	addi	a0,a0,20
   14dac:	03c5                	addi	t2,t2,17
   14dae:	02800667          	jalr	a2,40(zero) # 0 <main-0x10074>
   14db2:	0059                	c.nop	22
   14db4:	14ba                	slli	s1,s1,0x2e
   14db6:	1b5c2b07          	flw	fs6,437(s8)
   14dba:	201d                	jal	14de0 <h+0x290>
   14dbc:	2cd92daf          	0x2cd92daf
   14dc0:	2111                	jal	151c4 <h+0x674>
   14dc2:	29ce                	fld	fs3,208(sp)
   14dc4:	0791                	addi	a5,a5,4
   14dc6:	2644                	fld	fs1,136(a2)
   14dc8:	2ecd                	jal	151ba <h+0x66a>
   14dca:	1acb2d67          	0x1acb2d67
   14dce:	0489                	addi	s1,s1,2
   14dd0:	12b4                	addi	a3,sp,360
   14dd2:	28ae                	fld	fa7,200(sp)
   14dd4:	1a2d                	addi	s4,s4,-21
   14dd6:	2e42                	fld	ft8,16(sp)
   14dd8:	258b0c47          	0x258b0c47
   14ddc:	1258                	addi	a4,sp,292
   14dde:	05fd                	addi	a1,a1,31
   14de0:	2aec                	fld	fa1,208(a3)
   14de2:	010c                	addi	a1,sp,128
   14de4:	292e                	fld	fs2,200(sp)
   14de6:	1631                	addi	a2,a2,-20
   14de8:	23d1                	jal	153ac <sig+0x5c>
   14dea:	06c1                	addi	a3,a3,16
   14dec:	0c18                	addi	a4,sp,528
   14dee:	1df2                	slli	s11,s11,0x3c
   14df0:	1a3513ef          	jal	t2,66792 <__BSS_END__+0x4eb8e>
   14df4:	1ec1                	addi	t4,t4,-16
   14df6:	118d                	addi	gp,gp,-29
   14df8:	0c60                	addi	s0,sp,540
   14dfa:	25f0                	fld	fa2,200(a1)
   14dfc:	0cb5                	addi	s9,s9,13
   14dfe:	0d99                	addi	s11,s11,6
   14e00:	2679                	jal	1518e <h+0x63e>
   14e02:	2d55                	jal	154b6 <sig+0x166>
   14e04:	2b55                	jal	153b8 <sig+0x68>
   14e06:	10060b97          	auipc	s7,0x10060
   14e0a:	24f8                	fld	fa4,200(s1)
   14e0c:	2cd8                	fld	fa4,152(s1)
   14e0e:	21942f27          	fsw	fs9,542(s0)
   14e12:	298c194b          	fnmsub.s	fs2,fs8,fs8,ft5,rtz
   14e16:	03be                	slli	t2,t2,0xf
   14e18:	256a                	fld	fa0,152(sp)
   14e1a:	2c85                	jal	1508a <h+0x53a>
   14e1c:	1d55                	addi	s10,s10,-11
   14e1e:	1766                	slli	a4,a4,0x39
   14e20:	1ed5                	addi	t4,t4,-11
   14e22:	1d020393          	addi	t2,tp,464 # 1d0 <main-0xfea4>
   14e26:	19bc0757          	0x19bc0757
   14e2a:	0c920f8b          	0xc920f8b
   14e2e:	10b1                	addi	ra,ra,-20
   14e30:	2f6c                	fld	fa1,216(a4)
   14e32:	2334                	fld	fa3,64(a4)
   14e34:	0e19                	addi	t3,t3,6
   14e36:	2835274b          	fnmsub.s	fa4,fa0,ft3,ft5,rdn
   14e3a:	22c02abb          	0x22c02abb
   14e3e:	1dc6                	slli	s11,s11,0x31
   14e40:	1bc4                	addi	s1,sp,500
   14e42:	0a4e                	slli	s4,s4,0x13
   14e44:	23e5                	jal	1542c <sig+0xdc>
   14e46:	05cd                	addi	a1,a1,19
   14e48:	2b84                	fld	fs1,16(a5)
   14e4a:	18960807          	0x18960807
   14e4e:	2b90025b          	0x2b90025b
   14e52:	1ab1                	addi	s5,s5,-20
   14e54:	2e10                	fld	fa2,24(a2)
   14e56:	1d7d                	addi	s10,s10,-1
   14e58:	092206f3          	0x92206f3
   14e5c:	21f4                	fld	fa3,192(a1)
   14e5e:	2f6e                	fld	ft10,216(sp)
   14e60:	29ae                	fld	fs3,200(sp)
   14e62:	122310bb          	0x122310bb
   14e66:	13422a5b          	0x13422a5b
   14e6a:	03d9                	addi	t2,t2,22
   14e6c:	1b5b04af          	0x1b5b04af
   14e70:	1570                	addi	a2,sp,684
   14e72:	15dc                	addi	a5,sp,740
   14e74:	01c6                	slli	gp,gp,0x11
   14e76:	2146                	fld	ft2,80(sp)
   14e78:	0b3c                	addi	a5,sp,408
   14e7a:	10f9                	addi	ra,ra,-2
   14e7c:	053d                	addi	a0,a0,15
   14e7e:	2762                	fld	fa4,24(sp)
   14e80:	0071                	c.nop	28
   14e82:	1bcd                	addi	s7,s7,-13
   14e84:	2cee                	fld	fs9,216(sp)
   14e86:	05b50f6b          	0x5b50f6b
   14e8a:	1d7a                	slli	s10,s10,0x3e
   14e8c:	1408028f          	0x1408028f
   14e90:	2569232b          	0x2569232b
   14e94:	12bd                	addi	t0,t0,-17
   14e96:	2b0c                	fld	fa1,16(a4)
   14e98:	0a6a1cab          	0xa6a1cab
   14e9c:	1ef2                	slli	t4,t4,0x3c
   14e9e:	1a6a                	slli	s4,s4,0x3a
   14ea0:	0c0e                	slli	s8,s8,0x3
   14ea2:	27a32efb          	0x27a32efb
   14ea6:	00c9                	addi	ra,ra,18
   14ea8:	1fea                	slli	t6,t6,0x3a
   14eaa:	1898                	addi	a4,sp,112
   14eac:	2bb0                	fld	fa2,80(a5)
   14eae:	19262703          	lw	a4,402(a2) # 18ff0192 <__BSS_END__+0x18fd858e>
   14eb2:	06532d3b          	0x6532d3b
   14eb6:	2442                	fld	fs0,16(sp)
   14eb8:	13aa                	slli	t2,t2,0x2a
   14eba:	05af2137          	lui	sp,0x5af2
   14ebe:	0d94                	addi	a3,sp,720
   14ec0:	211413e3          	bne	s0,a7,158c6 <sig+0x576>
   14ec4:	2279                	jal	15052 <h+0x502>
   14ec6:	2329                	jal	153d0 <sig+0x80>
   14ec8:	2f4e                	fld	ft10,208(sp)
   14eca:	1369                	addi	t1,t1,-6
   14ecc:	12de                	slli	t0,t0,0x37
   14ece:	01e2                	slli	gp,gp,0x18
   14ed0:	0c850157          	0xc850157
   14ed4:	2eac                	fld	fa1,88(a3)
   14ed6:	15631957          	0x15631957
   14eda:	0108                	addi	a0,sp,128
   14edc:	1dc206b7          	lui	a3,0x1dc20
   14ee0:	218d                	jal	15342 <h+0x7f2>
   14ee2:	01c9                	addi	gp,gp,18
   14ee4:	0b6b2ac7          	fmsub.d	fs5,fs6,fs6,ft1,rdn
   14ee8:	18ce                	slli	a7,a7,0x33
   14eea:	12da                	slli	t0,t0,0x36
   14eec:	018c                	addi	a1,sp,192
   14eee:	0b75                	addi	s6,s6,29
   14ef0:	03c9                	addi	t2,t2,18
   14ef2:	18d4                	addi	a3,sp,116
   14ef4:	06bc                	addi	a5,sp,840
   14ef6:	2a52                	fld	fs4,272(sp)
   14ef8:	2d1a                	fld	fs10,384(sp)
   14efa:	0882160f          	0x882160f
   14efe:	24c1                	jal	151be <h+0x66e>
   14f00:	2ac0                	fld	fs0,144(a3)
   14f02:	0d61                	addi	s10,s10,24
   14f04:	1cb2                	slli	s9,s9,0x2c
   14f06:	08492a2f          	amoswap.w	s4,tp,(s2)
   14f0a:	0a940547          	fmsub.d	fa0,fs0,fs1,ft1,rne
   14f0e:	1182                	slli	gp,gp,0x20
   14f10:	0031                	c.nop	12
   14f12:	2b38                	fld	fa4,80(a4)
   14f14:	1ca0                	addi	s0,sp,632
   14f16:	12ee0ab3          	0x12ee0ab3
   14f1a:	0988                	addi	a0,sp,208
   14f1c:	03b0                	addi	a2,sp,456
   14f1e:	0ee4                	addi	s1,sp,860
   14f20:	1aff                	0x1aff
   14f22:	0205                	addi	tp,tp,1
   14f24:	0801                	addi	a6,a6,0
   14f26:	1ac1                	addi	s5,s5,-16
   14f28:	0e5e                	slli	t3,t3,0x17
   14f2a:	2739                	jal	15638 <sig+0x2e8>
   14f2c:	13a1                	addi	t2,t2,-24
   14f2e:	015c                	addi	a5,sp,132
   14f30:	0f9e                	slli	t6,t6,0x7
   14f32:	1d56                	slli	s10,s10,0x35
   14f34:	0111                	addi	sp,sp,4
   14f36:	2594                	fld	fa3,8(a1)
   14f38:	21ef1623          	sh	t5,524(t5) # 23bb6f64 <__BSS_END__+0x23b9f360>
   14f3c:	2452                	fld	fs0,272(sp)
   14f3e:	0819                	addi	a6,a6,6
   14f40:	2528                	fld	fa0,72(a0)
   14f42:	2c3c                	fld	fa5,88(s0)
   14f44:	1a82                	slli	s5,s5,0x20
   14f46:	15e6                	slli	a1,a1,0x39
   14f48:	28bd                	jal	14fc6 <h+0x476>
   14f4a:	2856                	fld	fa6,336(sp)
   14f4c:	2bc607ab          	0x2bc607ab
   14f50:	282e                	fld	fa6,200(sp)
   14f52:	031a                	slli	t1,t1,0x6
   14f54:	24e0                	fld	fs0,200(s1)
   14f56:	255f 2e47 03be      	0x3be2e47255f
   14f5c:	2ca4                	fld	fs1,88(s1)
   14f5e:	0fb82f3b          	0xfb82f3b
   14f62:	1556                	slli	a0,a0,0x35
   14f64:	0600                	addi	s0,sp,768
   14f66:	044d                	addi	s0,s0,19
   14f68:	1114                	addi	a3,sp,160
   14f6a:	0864                	addi	s1,sp,28
   14f6c:	0e8103c3          	fmadd.q	ft7,ft2,fs0,ft1,rne
   14f70:	0c95                	addi	s9,s9,5
   14f72:	1472                	slli	s0,s0,0x3c
   14f74:	0bc124b7          	lui	s1,0xbc12
   14f78:	2a38                	fld	fa4,80(a2)
   14f7a:	233514d3          	fsgnjn.d	fs1,fa0,fs3
   14f7e:	0312                	slli	t1,t1,0x4
   14f80:	0aa1                	addi	s5,s5,8
   14f82:	1d1d                	addi	s10,s10,-25
   14f84:	2660                	fld	fs0,200(a2)
   14f86:	2be9                	jal	15560 <sig+0x210>
   14f88:	27f2                	fld	fa5,280(sp)
   14f8a:	2e54                	fld	fa3,152(a2)
   14f8c:	1d3724f7          	0x1d3724f7
   14f90:	156d2c3f 128f18ec 	0x128f18ec156d2c3f
   14f98:	1d5e                	slli	s10,s10,0x37
   14f9a:	29e4                	fld	fs1,208(a1)
   14f9c:	1c532907          	flw	fs2,453(t1)
   14fa0:	2c21                	jal	151b8 <h+0x668>
   14fa2:	05fd                	addi	a1,a1,31
   14fa4:	041f 0cc2 1203      	0x12030cc2041f
   14faa:	1a64                	addi	s1,sp,316
   14fac:	01f5                	addi	gp,gp,29
   14fae:	0f58                	addi	a4,sp,916
   14fb0:	145604e7          	jalr	s1,325(a2)
   14fb4:	1135                	addi	sp,sp,-19
   14fb6:	0a31                	addi	s4,s4,12
   14fb8:	06ac                	addi	a1,sp,840
   14fba:	28522e97          	auipc	t4,0x28522
   14fbe:	0e1b088b          	0xe1b088b
   14fc2:	10c6                	slli	ra,ra,0x31
   14fc4:	02ec                	addi	a1,sp,332
   14fc6:	2f9a                	fld	ft11,384(sp)
   14fc8:	1bdd                	addi	s7,s7,-9
   14fca:	0a9d                	addi	s5,s5,7
   14fcc:	0962                	slli	s2,s2,0x18
   14fce:	2db4                	fld	fa3,88(a1)
   14fd0:	1c5e                	slli	s8,s8,0x37
   14fd2:	2cfe                	fld	fs9,472(sp)
   14fd4:	14e6                	slli	s1,s1,0x39
   14fd6:	1a1b11db          	0x1a1b11db
   14fda:	0c662763          	0xc662763
   14fde:	07a8                	addi	a0,sp,968
   14fe0:	0226                	slli	tp,tp,0x9
   14fe2:	2778190f          	0x2778190f
   14fe6:	2bcc                	fld	fa1,144(a5)
   14fe8:	069700af          	0x69700af
   14fec:	1424                	addi	s1,sp,552
   14fee:	1430                	addi	a2,sp,552
   14ff0:	0d06                	slli	s10,s10,0x1
   14ff2:	26f0                	fld	fa2,200(a3)
   14ff4:	15f0                	addi	a2,sp,748
   14ff6:	164a                	slli	a2,a2,0x32
   14ff8:	280d                	jal	1502a <h+0x4da>
   14ffa:	0e32                	slli	t3,t3,0xc
   14ffc:	087a                	slli	a6,a6,0x1e
   14ffe:	01cc                	addi	a1,sp,196
   15000:	0172                	slli	sp,sp,0x1c
   15002:	02d4                	addi	a3,sp,324
   15004:	0f96                	slli	t6,t6,0x5
   15006:	0f89                	addi	t6,t6,2
   15008:	1762                	slli	a4,a4,0x38
   1500a:	2e531c7b          	0x2e531c7b
   1500e:	1484                	addi	s1,sp,608
   15010:	14c4                	addi	s1,sp,612
   15012:	2479                	jal	152a0 <h+0x750>
   15014:	27ce1c6f          	jal	s8,f6290 <__BSS_END__+0xde68c>
   15018:	23e2                	fld	ft7,24(sp)
   1501a:	068a                	slli	a3,a3,0x2
   1501c:	2b16                	fld	fs6,320(sp)
   1501e:	25382fab          	0x25382fab
   15022:	27d5                	jal	15806 <sig+0x4b6>
   15024:	01e304af          	0x1e304af
   15028:	2e7c                	fld	fa5,216(a2)
   1502a:	154a                	slli	a0,a0,0x32
   1502c:	25f6                	fld	fa1,344(sp)
   1502e:	14e1                	addi	s1,s1,-8
   15030:	190e                	slli	s2,s2,0x23
   15032:	2b02                	fld	fs6,0(sp)
   15034:	24c0                	fld	fs0,136(s1)
   15036:	169f 161a 0669      	0x669161a169f
   1503c:	0bed                	addi	s7,s7,27
   1503e:	25e8                	fld	fa0,200(a1)
   15040:	082411c3          	fmadd.s	ft3,fs0,ft2,ft1,rtz
   15044:	0956                	slli	s2,s2,0x15
   15046:	109c                	addi	a5,sp,96
   15048:	1f16                	slli	t5,t5,0x25
   1504a:	09fa                	slli	s3,s3,0x1e
   1504c:	107617ab          	0x107617ab
   15050:	2171                	jal	154dc <sig+0x18c>
   15052:	267209d3          	fsgnj.q	fs3,ft4,ft7
   15056:	1cad                	addi	s9,s9,-21
   15058:	23c0                	fld	fs0,128(a5)
   1505a:	0799                	addi	a5,a5,6
   1505c:	195d                	addi	s2,s2,-9
   1505e:	27752103          	lw	sp,631(a0)
   15062:	1909                	addi	s2,s2,-30
   15064:	1e05                	addi	t3,t3,-31
   15066:	1bb1                	addi	s7,s7,-20
   15068:	111b2333          	0x111b2333
   1506c:	003d                	c.nop	15
   1506e:	06ad                	addi	a3,a3,11
   15070:	174a                	slli	a4,a4,0x32
   15072:	22ab1c03          	lh	s8,554(s6)
   15076:	19de                	slli	s3,s3,0x37
   15078:	14d5                	addi	s1,s1,-11
   1507a:	1d5f 051b 1e93      	0x1e93051b1d5f
   15080:	0f2b20af          	amoswap.w.aqrl	ra,s2,(s6)
   15084:	261c21fb          	0x261c21fb
   15088:	1790                	addi	a2,sp,992
   1508a:	ffff24ef          	jal	s1,8088 <main-0x7fec>
   1508e:	ffff                	0xffff
   15090:	ffff                	0xffff
   15092:	ffff                	0xffff
   15094:	ffff                	0xffff
   15096:	ffff                	0xffff
   15098:	ffff                	0xffff
   1509a:	ffff                	0xffff
   1509c:	ffff                	0xffff
   1509e:	ffff                	0xffff
   150a0:	ffff                	0xffff
   150a2:	ffff                	0xffff
   150a4:	ffff                	0xffff
   150a6:	ffff                	0xffff
   150a8:	ffff                	0xffff
   150aa:	ffff                	0xffff
   150ac:	ffff                	0xffff
   150ae:	ffff                	0xffff
   150b0:	ffff                	0xffff
   150b2:	ffff                	0xffff
   150b4:	ffff                	0xffff
   150b6:	ffff                	0xffff
   150b8:	ffff                	0xffff
   150ba:	ffff                	0xffff
   150bc:	ffff                	0xffff
   150be:	ffff                	0xffff
   150c0:	ffff                	0xffff
   150c2:	ffff                	0xffff
   150c4:	ffff                	0xffff
   150c6:	ffff                	0xffff
   150c8:	ffff                	0xffff
   150ca:	ffff                	0xffff
   150cc:	ffff                	0xffff
   150ce:	ffff                	0xffff
   150d0:	ffff                	0xffff
   150d2:	ffff                	0xffff
   150d4:	ffff                	0xffff
   150d6:	ffff                	0xffff
   150d8:	ffff                	0xffff
   150da:	ffff                	0xffff
   150dc:	ffff                	0xffff
   150de:	ffff                	0xffff
   150e0:	ffff                	0xffff
   150e2:	ffff                	0xffff
   150e4:	ffff                	0xffff
   150e6:	ffff                	0xffff
   150e8:	ffff                	0xffff
   150ea:	0000                	unimp
   150ec:	0000                	unimp
   150ee:	0000                	unimp
   150f0:	00000003          	lb	zero,0(zero) # 0 <main-0x10074>
   150f4:	0000                	unimp
   150f6:	0000                	unimp
   150f8:	00000007          	0x7
   150fc:	0000                	unimp
   150fe:	0000                	unimp
   15100:	0001                	nop
	...
   1510e:	c02a                	sw	a0,0(sp)
   15110:	0000                	unimp
   15112:	0080                	addi	s0,sp,64
   15114:	0000                	unimp
   15116:	0000                	unimp
   15118:	0000                	unimp
   1511a:	8200                	0x8200
   1511c:	7fa4                	flw	fs1,120(a5)
	...
   15126:	402c                	lw	a1,64(s0)
   15128:	0000                	unimp
   1512a:	0080                	addi	s0,sp,64
	...
   15134:	0001                	nop
   15136:	0200                	addi	s0,sp,256
   15138:	9268                	0x9268
   1513a:	00010a8f          	0x10a8f
   1513e:	0000                	unimp
   15140:	8a00                	0x8a00
   15142:	00010a8f          	0x10a8f
   15146:	0000                	unimp
   15148:	9250                	0x9250
   1514a:	00010a8f          	0x10a8f
   1514e:	0000                	unimp
   15150:	0000                	unimp
   15152:	8200                	0x8200
   15154:	7fa4                	flw	fs1,120(a5)
   15156:	0000                	unimp
   15158:	0008                	0x8
   1515a:	0000                	unimp
   1515c:	0000                	unimp
   1515e:	0000                	unimp
   15160:	b9a0                	fsd	fs0,112(a1)
   15162:	b575                	j	1500e <h+0x4be>
   15164:	00007ff7          	0x7ff7
   15168:	0e85                	addi	t4,t4,1
   1516a:	13a1                	addi	t2,t2,-24
   1516c:	7ff8                	flw	fa4,124(a5)
   1516e:	0000                	unimp
   15170:	a408                	fsd	fa0,8(s0)
   15172:	db4a400b          	0xdb4a400b
   15176:	1000c05b          	0x1000c05b
   1517a:	c000                	sw	s0,0(s0)
   1517c:	4000                	lw	s0,0(s0)
   1517e:	fffff6bf 00000000 	0xfffff6bf
   15186:	4028                	lw	a0,64(s0)
   15188:	7000                	flw	fs0,32(s0)
   1518a:	0a8e                	slli	s5,s5,0x3
   1518c:	0001                	nop
   1518e:	0000                	unimp
   15190:	0008                	0x8
	...
   151a2:	0000                	unimp
   151a4:	0008                	0x8
   151a6:	0000                	unimp
   151a8:	9268                	0x9268
   151aa:	00010a8f          	0x10a8f
   151ae:	0000                	unimp
   151b0:	8a00                	0x8a00
   151b2:	00010a8f          	0x10a8f
	...
   151be:	0000                	unimp
   151c0:	b380                	fsd	fs0,32(a5)
   151c2:	0a8e                	slli	s5,s5,0x3
   151c4:	0001                	nop
   151c6:	0000                	unimp
   151c8:	f418                	fsw	fa4,40(s0)
   151ca:	5541                	li	a0,-16
   151cc:	7ff8                	flw	fa4,124(a5)
   151ce:	0000                	unimp
   151d0:	1000                	addi	s0,sp,32
   151d2:	0000                	unimp
   151d4:	0000                	unimp
   151d6:	0000                	unimp
   151d8:	c700                	sw	s0,8(a4)
   151da:	b575                	j	15086 <h+0x536>
   151dc:	00007ff7          	0x7ff7
	...
   151e8:	7000                	flw	fs0,32(s0)
   151ea:	0a8e                	slli	s5,s5,0x3
   151ec:	0001                	nop
   151ee:	0000                	unimp
   151f0:	b9d0                	fsd	fa2,176(a1)
   151f2:	b575                	j	1509e <h+0x54e>
   151f4:	00007ff7          	0x7ff7
   151f8:	07d2                	slli	a5,a5,0x14
   151fa:	13a1                	addi	t2,t2,-24
   151fc:	7ff8                	flw	fa4,124(a5)
   151fe:	0000                	unimp
   15200:	f418                	fsw	fa4,40(s0)
   15202:	5541                	li	a0,-16
   15204:	7ff8                	flw	fa4,124(a5)
   15206:	0000                	unimp
   15208:	1000                	addi	s0,sp,32
   1520a:	0000                	unimp
   1520c:	0000                	unimp
   1520e:	0000                	unimp
   15210:	0001                	nop
   15212:	0000                	unimp
   15214:	0000                	unimp
   15216:	0000                	unimp
   15218:	8000                	0x8000
   1521a:	7ff85543          	fmadd.q	fa0,fa6,ft11,fa5,unknown
   1521e:	0000                	unimp
   15220:	ba10                	fsd	fa2,48(a2)
   15222:	b575                	j	150ce <h+0x57e>
   15224:	00007ff7          	0x7ff7
   15228:	bad6                	fsd	fs5,368(sp)
   1522a:	13a2                	slli	t2,t2,0x28
   1522c:	7ff8                	flw	fa4,124(a5)
   1522e:	0000                	unimp
   15230:	0001                	nop
   15232:	0000                	unimp
   15234:	0000                	unimp
   15236:	0000                	unimp
   15238:	f418                	fsw	fa4,40(s0)
   1523a:	5541                	li	a0,-16
   1523c:	7ff8                	flw	fa4,124(a5)
   1523e:	0000                	unimp
   15240:	0801                	addi	a6,a6,0
   15242:	0000                	unimp
   15244:	0000                	unimp
   15246:	0000                	unimp
   15248:	c788                	sw	a0,8(a5)
   1524a:	b575                	j	150f6 <h+0x5a6>
   1524c:	00007ff7          	0x7ff7
   15250:	1000                	addi	s0,sp,32
   15252:	0000                	unimp
   15254:	0000                	unimp
   15256:	0000                	unimp
   15258:	0001                	nop
   1525a:	0000                	unimp
   1525c:	0000                	unimp
   1525e:	0000                	unimp
   15260:	ba60                	fsd	fs0,240(a2)
   15262:	b575                	j	1510e <h+0x5be>
   15264:	00007ff7          	0x7ff7
   15268:	7222                	flw	ft4,40(sp)
   1526a:	13ad                	addi	t2,t2,-21
   1526c:	7ff8                	flw	fa4,124(a5)
   1526e:	0000                	unimp
   15270:	ba50                	fsd	fa2,176(a2)
   15272:	b575                	j	1511e <h+0x5ce>
   15274:	00007ff7          	0x7ff7
   15278:	13ad2f83          	lw	t6,314(s10)
   1527c:	7ff8                	flw	fa4,124(a5)
   1527e:	0000                	unimp
   15280:	8200                	0x8200
   15282:	8200                	0x8200
   15284:	7fa4                	flw	fs1,120(a5)
   15286:	0000                	unimp
   15288:	00000007          	0x7
	...
   15298:	f418                	fsw	fa4,40(s0)
   1529a:	5541                	li	a0,-16
   1529c:	7ff8                	flw	fa4,124(a5)
   1529e:	0000                	unimp
   152a0:	ba80                	fsd	fs0,48(a3)
   152a2:	b575                	j	1514e <h+0x5fe>
   152a4:	00007ff7          	0x7ff7
   152a8:	13ad0c03          	lb	s8,314(s10)
   152ac:	7ff8                	flw	fa4,124(a5)
   152ae:	0000                	unimp
   152b0:	0001                	nop
   152b2:	0000                	unimp
   152b4:	0000                	unimp
   152b6:	0000                	unimp
   152b8:	2efe                	fld	ft9,472(sp)
   152ba:	13b4                	addi	a3,sp,488
   152bc:	7ff8                	flw	fa4,124(a5)
   152be:	0000                	unimp
   152c0:	0001                	nop
   152c2:	0000                	unimp
   152c4:	0000                	unimp
   152c6:	0000                	unimp
   152c8:	bb10                	fsd	fa2,48(a4)
   152ca:	b575                	j	15176 <h+0x626>
   152cc:	00007ff7          	0x7ff7
   152d0:	bad0                	fsd	fa2,176(a3)
   152d2:	b575                	j	1517e <h+0x62e>
   152d4:	00007ff7          	0x7ff7
   152d8:	441a                	lw	s0,132(sp)
   152da:	13ac                	addi	a1,sp,488
   152dc:	7ff8                	flw	fa4,124(a5)
	...
   152e6:	0000                	unimp
   152e8:	f418                	fsw	fa4,40(s0)
   152ea:	5541                	li	a0,-16
   152ec:	7ff8                	flw	fa4,124(a5)
	...
   152f6:	0000                	unimp
   152f8:	bb50                	fsd	fa2,176(a4)
   152fa:	b575                	j	151a6 <h+0x656>
   152fc:	00007ff7          	0x7ff7
   15300:	bad0                	fsd	fa2,176(a3)
   15302:	b575                	j	151ae <h+0x65e>
   15304:	00007ff7          	0x7ff7
   15308:	0d36                	slli	s10,s10,0xd
   1530a:	13ad                	addi	t2,t2,-21
   1530c:	7ff8                	flw	fa4,124(a5)
   1530e:	0000                	unimp
   15310:	ffff                	0xffff
   15312:	ffff                	0xffff
   15314:	0000                	unimp
   15316:	0000                	unimp
   15318:	4898                	lw	a4,16(s1)
   1531a:	5544                	lw	s1,44(a0)
   1531c:	7ff8                	flw	fa4,124(a5)
   1531e:	0000                	unimp
   15320:	bb30                	fsd	fa2,112(a4)
   15322:	b575                	j	151ce <h+0x67e>
   15324:	00007ff7          	0x7ff7
   15328:	168a                	slli	a3,a3,0x22
   1532a:	7ff813af          	0x7ff813af
   1532e:	0000                	unimp
   15330:	baf0                	fsd	fa2,240(a3)
   15332:	b575                	j	151de <h+0x68e>
   15334:	00007ff7          	0x7ff7
   15338:	0002                	c.slli64	zero
   1533a:	0000                	unimp
   1533c:	0000                	unimp
   1533e:	0000                	unimp
   15340:	bb4c                	fsd	fa1,176(a4)
   15342:	b575                	j	151ee <h+0x69e>
   15344:	00007ff7          	0x7ff7
   15348:	9a98                	0x9a98
   1534a:	00010a7b          	0x10a7b
	...

00015350 <sig>:
   15350:	00f8                	addi	a4,sp,76
   15352:	00a1                	addi	ra,ra,8
   15354:	ff64                	fsw	fs1,124(a4)
   15356:	ff1f 0076 012d      	0x12d0076ff1f
   1535c:	00fd                	addi	ra,ra,31
   1535e:	005c                	addi	a5,sp,4
   15360:	005c00c3          	fmadd.s	ft1,fs8,ft5,ft0,rne
   15364:	fff6                	fsw	ft9,252(sp)
   15366:	006dfff3          	csrrci	t6,0x6,27
   1536a:	013bff9b          	0x13bff9b
   1536e:	ffc4                	fsw	fs1,60(a5)
   15370:	008effdb          	0x8effdb
   15374:	ff51fffb          	0xff51fffb
   15378:	fec4ff3b          	0xfec4ff3b
   1537c:	ffd9                	bnez	a5,1531a <h+0x7ca>
   1537e:	0071                	c.nop	28
   15380:	ff2a                	fsw	fa0,188(sp)
   15382:	009e                	slli	ra,ra,0x7
   15384:	ff61                	bnez	a4,1535c <sig+0xc>
   15386:	ff32                	fsw	fa2,188(sp)
   15388:	ff1e0003          	lb	zero,-15(t3) # 1ab55437 <__BSS_END__+0x1ab3d833>
   1538c:	ffd0                	fsw	fa2,60(a5)
   1538e:	ff42                	fsw	fa6,188(sp)
   15390:	ffda                	fsw	fs6,252(sp)
   15392:	ffbd                	bnez	a5,15310 <h+0x7c0>
   15394:	005d                	c.nop	23
   15396:	ff2d00fb          	0xff2d00fb
   1539a:	002fffbf fffe0088 	0xfffe0088002fffbf
   153a2:	00a8                	addi	a0,sp,72
   153a4:	00d1                	addi	ra,ra,20
   153a6:	007d                	c.nop	31
   153a8:	00d9                	addi	ra,ra,22
   153aa:	ff6f0103          	lb	sp,-10(t5)
   153ae:	ffea                	fsw	fs10,252(sp)
   153b0:	ff81                	bnez	a5,152c8 <h+0x778>
   153b2:	ff8aff57          	0xff8aff57
   153b6:	ffbc                	fsw	fa5,120(a5)
   153b8:	0011                	c.nop	4
   153ba:	ffac                	fsw	fa1,120(a5)
   153bc:	feb6                	fsw	fa3,124(sp)
   153be:	002e                	c.slli	zero,0xb
   153c0:	ff9e005b          	0xff9e005b
   153c4:	ffc6                	fsw	fa7,252(sp)
   153c6:	0045                	c.nop	17
   153c8:	ff00                	fsw	fs0,56(a4)
   153ca:	ffd1ffa3          	0xffd1ffa3
   153ce:	002e                	c.slli	zero,0xb
   153d0:	00e8                	addi	a0,sp,76
   153d2:	00b8fe47          	fmsub.s	ft8,fa7,fa1,ft0
   153d6:	fff3ff0f          	0xfff3ff0f
   153da:	0102                	c.slli64	sp
   153dc:	00d5ff23          	0xd5ff23
   153e0:	00fc                	addi	a5,sp,76
   153e2:	0034                	addi	a3,sp,8
   153e4:	ff710113          	addi	sp,sp,-9 # 5af1ff7 <__BSS_END__+0x5ada3f3>
   153e8:	ffd6                	fsw	fs5,252(sp)
   153ea:	0034                	addi	a3,sp,8
   153ec:	0160                	addi	s0,sp,140
   153ee:	00dc                	addi	a5,sp,68
   153f0:	ff9eff0f          	0xff9eff0f
   153f4:	fff9                	bnez	a5,153d2 <sig+0x82>
   153f6:	0084                	addi	s1,sp,64
   153f8:	013b0037          	lui	zero,0x13b0
   153fc:	00a5                	addi	ra,ra,9
   153fe:	ff6c                	fsw	fa1,124(a4)
   15400:	ffbe                	fsw	fa5,252(sp)
   15402:	ffaa00db          	0xffaa00db
   15406:	fff2                	fsw	ft8,252(sp)
   15408:	009e                	slli	ra,ra,0x7
   1540a:	ffec                	fsw	fa1,124(a5)
   1540c:	0131                	addi	sp,sp,12
   1540e:	002e                	c.slli	zero,0xb
   15410:	fe0d                	bnez	a2,1534a <h+0x7fa>
   15412:	ffa8                	fsw	fa0,120(a5)
   15414:	ff6a                	fsw	fs10,188(sp)
   15416:	00ba                	slli	ra,ra,0xe
   15418:	004e                	c.slli	zero,0x13
   1541a:	0018                	0x18
   1541c:	ff9e                	fsw	ft7,252(sp)
   1541e:	ff55                	bnez	a4,153da <sig+0x8a>
   15420:	ff430013          	addi	zero,t1,-12
   15424:	005c                	addi	a5,sp,4
   15426:	ffc1                	bnez	a5,153be <sig+0x6e>
   15428:	ff80                	fsw	fs0,56(a5)
   1542a:	006c                	addi	a1,sp,12
   1542c:	ff01                	bnez	a4,15344 <h+0x7f4>
   1542e:	009dffd7          	0x9dffd7
   15432:	ffc0                	fsw	fs0,60(a5)
   15434:	ff06                	fsw	ft1,188(sp)
   15436:	ff3a                	fsw	fa4,188(sp)
   15438:	ffa8                	fsw	fa0,120(a5)
   1543a:	fffcff43          	fmadd.q	ft10,fs9,ft11,ft11
   1543e:	ff3d                	bnez	a4,153bc <sig+0x6c>
   15440:	ffd0                	fsw	fa2,60(a5)
   15442:	00b2                	slli	ra,ra,0xc
   15444:	ff9d                	bnez	a5,15382 <sig+0x32>
   15446:	0068                	addi	a0,sp,12
   15448:	004c                	addi	a1,sp,4
   1544a:	001a00a3          	sb	ra,1(s4)
   1544e:	ff2fff97          	auipc	t6,0xff2ff
   15452:	fffb0093          	addi	ra,s6,-1
   15456:	00b8                	addi	a4,sp,72
   15458:	ffdd                	bnez	a5,15416 <sig+0xc6>
   1545a:	0008                	0x8
   1545c:	00bf002b          	0xbf002b
   15460:	ff18                	fsw	fa4,56(a4)
   15462:	fec900cf          	fnmadd.q	ft1,fs2,fa2,ft11,rne
   15466:	fffc                	fsw	fa5,124(a5)
   15468:	ffa0                	fsw	fs0,120(a5)
   1546a:	fff6                	fsw	ft9,252(sp)
   1546c:	ff5c                	fsw	fa5,60(a4)
   1546e:	ff14                	fsw	fa3,56(a4)
   15470:	fe5c                	fsw	fa5,60(a2)
   15472:	0079005b          	0x79005b
   15476:	00b4000f          	0xb4000f
   1547a:	0079                	c.nop	30
   1547c:	ffb8011b          	0xffb8011b
   15480:	ffd30183          	lb	gp,-3(t1)
   15484:	ff68                	fsw	fa0,124(a4)
   15486:	0078                	addi	a4,sp,12
   15488:	00a0                	addi	s0,sp,72
   1548a:	ff74ffa3          	0xff74ffa3
   1548e:	0188                	addi	a0,sp,192
   15490:	0148                	addi	a0,sp,132
   15492:	0170                	addi	a2,sp,140
   15494:	00a00087          	0xa00087
   15498:	fff1                	bnez	a5,15474 <sig+0x124>
   1549a:	0096                	slli	ra,ra,0x5
   1549c:	feda                	fsw	fs6,124(sp)
   1549e:	ffa200fb          	0xffa200fb
   154a2:	00020097          	auipc	ra,0x20
   154a6:	ff3fffc3          	fmadd.q	ft11,ft11,fs3,ft11
   154aa:	fed0                	fsw	fa2,60(a3)
   154ac:	00ce                	slli	ra,ra,0x13
   154ae:	ff84                	fsw	fs1,56(a5)
   154b0:	ffee                	fsw	fs11,252(sp)
   154b2:	003cff63          	bgeu	s9,gp,154d0 <sig+0x180>
   154b6:	ffcf0067          	jr	-4(t5)
   154ba:	ff2e                	fsw	fa1,188(sp)
   154bc:	0034ffb7          	lui	t6,0x34f
   154c0:	ffb8                	fsw	fa4,120(a5)
   154c2:	005c                	addi	a5,sp,4
   154c4:	01880057          	0x1880057
   154c8:	0015                	c.nop	5
   154ca:	01a2                	slli	gp,gp,0x8
   154cc:	ffe4ffb3          	0xffe4ffb3
   154d0:	ff59                	bnez	a4,1546e <sig+0x11e>
   154d2:	ff98                	fsw	fa4,56(a5)
   154d4:	ffccffaf          	0xffccffaf
   154d8:	00b4                	addi	a3,sp,72
   154da:	006a                	c.slli	zero,0x1a
   154dc:	0084                	addi	s1,sp,64
   154de:	0026                	c.slli	zero,0x9
   154e0:	0039                	c.nop	14
   154e2:	0059                	c.nop	22
   154e4:	fe98                	fsw	fa4,56(a3)
   154e6:	ff6afe77          	0xff6afe77
   154ea:	008b00db          	0x8b00db
   154ee:	ff7a                	fsw	ft10,188(sp)
   154f0:	0135                	addi	sp,sp,13
   154f2:	003200d3          	fadd.s	ft1,ft4,ft3,rne
   154f6:	0035                	c.nop	13
   154f8:	fef4                	fsw	fa3,124(a3)
   154fa:	ffed                	bnez	a5,154f4 <sig+0x1a4>
   154fc:	005c0073          	0x5c0073
   15500:	ff9f ff8c fffb      	0xfffbff8cff9f
   15506:	0088                	addi	a0,sp,64
   15508:	ff81                	bnez	a5,15420 <sig+0xd0>
   1550a:	002d                	c.nop	11
   1550c:	ff92                	fsw	ft4,252(sp)
   1550e:	00f2                	slli	ra,ra,0x1c
   15510:	012cffdb          	0x12cffdb
   15514:	0006                	c.slli	zero,0x1
   15516:	0014                	0x14
   15518:	005a                	c.slli	zero,0x16
   1551a:	ff88                	fsw	fa0,56(a5)
   1551c:	0038                	addi	a4,sp,8
   1551e:	00f2ffe7          	0xf2ffe7
   15522:	000d0013          	mv	zero,s10
   15526:	007c                	addi	a5,sp,12
   15528:	003d                	c.nop	15
   1552a:	ff32                	fsw	fa2,188(sp)
   1552c:	ff00                	fsw	fs0,56(a4)
   1552e:	014e                	slli	sp,sp,0x13
   15530:	001c                	0x1c
   15532:	ffba                	fsw	fa4,252(sp)
   15534:	ffac                	fsw	fa1,120(a5)
   15536:	ff66                	fsw	fs9,188(sp)
   15538:	0025                	c.nop	9
   1553a:	00b6                	slli	ra,ra,0xd
   1553c:	ff8c0003          	lb	zero,-8(s8)
   15540:	0021                	c.nop	8
   15542:	fef1                	bnez	a3,1551e <sig+0x1ce>
   15544:	ff92                	fsw	ft4,252(sp)
   15546:	00c4                	addi	s1,sp,68
   15548:	005d                	c.nop	23
   1554a:	0077ff67          	0x77ff67
   1554e:	ff86                	fsw	ft1,252(sp)
   15550:	009400a3          	sb	s1,1(s0)
   15554:	ffd2                	fsw	fs4,252(sp)
   15556:	000b0133          	add	sp,s6,zero
   1555a:	00c6fffb          	0xc6fffb
   1555e:	0074ff03          	0x74ff03
   15562:	fff0                	fsw	fa2,124(a5)
   15564:	005c                	addi	a5,sp,4
   15566:	0042                	c.slli	zero,0x10
   15568:	ff9e0127          	0xff9e0127
   1556c:	ffc9                	bnez	a5,15506 <sig+0x1b6>
   1556e:	008d                	addi	ra,ra,3
   15570:	ffe5                	bnez	a5,15568 <sig+0x218>
   15572:	00e6                	slli	ra,ra,0x19
   15574:	0091                	addi	ra,ra,4
   15576:	00ec008f          	0xec008f
   1557a:	0164                	addi	s1,sp,140
   1557c:	0066                	c.slli	zero,0x19
   1557e:	006e                	c.slli	zero,0x1b
   15580:	0061                	c.nop	24
   15582:	005a                	c.slli	zero,0x16
   15584:	ffed                	bnez	a5,1557e <sig+0x22e>
   15586:	ffbd                	bnez	a5,15504 <sig+0x1b4>
   15588:	ff08                	fsw	fa0,56(a4)
   1558a:	fedf 0098 ff0e      	0xff0e0098fedf
   15590:	fea9                	bnez	a3,154ea <sig+0x19a>
   15592:	00cbff43          	fmadd.s	ft10,fs7,fa2,ft0
   15596:	0102                	c.slli64	sp
   15598:	ff8d                	bnez	a5,154d2 <sig+0x182>
   1559a:	ffb600a7          	0xffb600a7
   1559e:	ff7e                	fsw	ft11,188(sp)
   155a0:	ffc3ff37          	lui	t5,0xffc3f
   155a4:	0208                	addi	a0,sp,256
   155a6:	fec2                	fsw	fa6,124(sp)
   155a8:	0058ff73          	csrrci	t5,utvec,17
   155ac:	004e                	c.slli	zero,0x13
   155ae:	ff5a                	fsw	fs6,188(sp)
   155b0:	ff81fef7          	0xff81fef7
   155b4:	006c                	addi	a1,sp,12
   155b6:	00230043          	fmadd.s	ft0,ft6,ft2,ft0,rne
   155ba:	00d0                	addi	a2,sp,68
   155bc:	ffb6                	fsw	fa3,252(sp)
   155be:	003c                	addi	a5,sp,8
   155c0:	004c                	addi	a1,sp,4
   155c2:	00ec                	addi	a1,sp,76
   155c4:	ff0d                	bnez	a4,154fe <sig+0x1ae>
   155c6:	ff89                	bnez	a5,154e0 <sig+0x190>
   155c8:	fff1                	bnez	a5,155a4 <sig+0x254>
   155ca:	019d                	addi	gp,gp,7
   155cc:	009affbf 003000cf 	0x3000cf009affbf
   155d4:	0145006b          	0x145006b
   155d8:	0154                	addi	a3,sp,132
   155da:	0106                	slli	sp,sp,0x1
   155dc:	fe8a                	fsw	ft2,124(sp)
   155de:	0111                	addi	sp,sp,4
   155e0:	0038                	addi	a4,sp,8
   155e2:	ff7a                	fsw	ft10,188(sp)
   155e4:	00ad00cb          	fnmsub.s	ft1,fs10,fa0,ft0,rne
   155e8:	fe6f0037          	lui	zero,0xfe6f0
   155ec:	0010                	0x10
   155ee:	ffb2                	fsw	fa2,252(sp)
   155f0:	ff8affcf          	fnmadd.q	ft11,fs5,fs8,ft11
   155f4:	ff86                	fsw	ft1,252(sp)
   155f6:	0039                	c.nop	14
   155f8:	003cff57          	0x3cff57
   155fc:	ff9c                	fsw	fa5,56(a5)
   155fe:	00a2                	slli	ra,ra,0x8
   15600:	0064ff4f          	fnmadd.s	ft10,fs1,ft6,ft0
   15604:	0094                	addi	a3,sp,64
   15606:	0002                	c.slli64	zero
   15608:	0066                	c.slli	zero,0x19
   1560a:	00770013          	addi	zero,a4,7 # 25f82007 <__BSS_END__+0x25f6a403>
   1560e:	002f002f          	0x2f002f
   15612:	0004                	0x4
   15614:	ff6cff77          	0xff6cff77
   15618:	ff36                	fsw	fa3,188(sp)
   1561a:	ff58                	fsw	fa4,60(a4)
   1561c:	ff36                	fsw	fa3,188(sp)
   1561e:	004a                	c.slli	zero,0x12
   15620:	ff6c                	fsw	fa1,124(a4)
   15622:	0029                	c.nop	10
   15624:	00a2ff43          	fmadd.s	ft10,ft5,fa0,ft0
   15628:	00de                	slli	ra,ra,0x17
   1562a:	0005005b          	0x5005b
   1562e:	ff18                	fsw	fa4,56(a4)
   15630:	00de0077          	0xde0077
   15634:	00b8                	addi	a4,sp,72
   15636:	ff41                	bnez	a4,155ce <sig+0x27e>
   15638:	feb0                	fsw	fa2,120(a3)
   1563a:	0070                	addi	a2,sp,12
   1563c:	005f ffed fefa      	0xfefaffed005f
   15642:	ff19feeb          	0xff19feeb
   15646:	fe33010b          	0xfe33010b
   1564a:	feda                	fsw	fs6,124(sp)
   1564c:	0165ff2b          	0x165ff2b
   15650:	00cd                	addi	ra,ra,19
   15652:	003e                	c.slli	zero,0xf
   15654:	0164                	addi	s1,sp,140
   15656:	0104                	addi	s1,sp,128
   15658:	ff44ffbb          	0xff44ffbb
   1565c:	0006010b          	0x6010b
   15660:	ffea                	fsw	fs10,252(sp)
   15662:	0026                	c.slli	zero,0x9
   15664:	ffa0                	fsw	fs0,120(a5)
   15666:	ff85003b          	0xff85003b
   1566a:	ffe6                	fsw	fs9,252(sp)
   1566c:	ffe6                	fsw	fs9,252(sp)
   1566e:	007d                	c.nop	31
   15670:	ff8a                	fsw	ft2,252(sp)
   15672:	0069                	c.nop	26
   15674:	0156                	slli	sp,sp,0x15
   15676:	fff2                	fsw	ft8,252(sp)
   15678:	00c60013          	addi	zero,a2,12
   1567c:	ffc1                	bnez	a5,15614 <sig+0x2c4>
   1567e:	fffa                	fsw	ft10,252(sp)
   15680:	ffb8                	fsw	fa4,120(a5)
   15682:	ffa9                	bnez	a5,155dc <sig+0x28c>
   15684:	feee0077          	0xfeee0077
   15688:	feda                	fsw	fs6,124(sp)
   1568a:	00f9                	addi	ra,ra,30
   1568c:	ff68ff47          	fmsub.q	ft10,fa7,fs6,ft11
   15690:	002e                	c.slli	zero,0xb
   15692:	00d0                	addi	a2,sp,68
   15694:	0000                	unimp
   15696:	0036                	c.slli	zero,0xd
   15698:	0015                	c.nop	5
   1569a:	00b9                	addi	ra,ra,14
   1569c:	002d                	c.nop	11
   1569e:	00010037          	lui	zero,0x10
   156a2:	00b9                	addi	ra,ra,14
   156a4:	ffc9                	bnez	a5,1563e <sig+0x2ee>
   156a6:	ffb1ff33          	0xffb1ff33
   156aa:	ffbe                	fsw	fa5,252(sp)
   156ac:	011d                	addi	sp,sp,7
   156ae:	ffcd                	bnez	a5,15668 <sig+0x318>
   156b0:	ff7a                	fsw	ft10,188(sp)
   156b2:	ffd2                	fsw	fs4,252(sp)
   156b4:	ff82                	fsw	ft0,252(sp)
   156b6:	000d                	c.nop	3
   156b8:	007e                	c.slli	zero,0x1f
   156ba:	0189000b          	0x189000b
   156be:	008e00a7          	0x8e00a7
   156c2:	ff49                	bnez	a4,1565c <sig+0x30c>
   156c4:	ff59                	bnez	a4,15662 <sig+0x312>
   156c6:	ffb1                	bnez	a5,15622 <sig+0x2d2>
   156c8:	ffa7ffcb          	fnmsub.q	ft11,fa5,fs10,ft11
   156cc:	0038                	addi	a4,sp,8
   156ce:	ffcc                	fsw	fa1,60(a5)
   156d0:	0075                	c.nop	29
   156d2:	0019                	c.nop	6
   156d4:	0005                	c.nop	1
   156d6:	ff25003f ffa40067 	0xffa40067ff25003f
   156de:	ffe6                	fsw	fs9,252(sp)
   156e0:	0002                	c.slli64	zero
   156e2:	00df ff5b 0184      	0x184ff5b00df
   156e8:	ffee                	fsw	fs11,252(sp)
   156ea:	0081                	addi	ra,ra,0
   156ec:	fffaffd3          	0xfffaffd3
   156f0:	ff4c0113          	addi	sp,s8,-12
   156f4:	00f0                	addi	a2,sp,76
   156f6:	00990077          	0x990077
   156fa:	ff42                	fsw	fa6,188(sp)
   156fc:	ff82                	fsw	ft0,252(sp)
   156fe:	0121                	addi	sp,sp,8
   15700:	ffe5                	bnez	a5,156f8 <sig+0x3a8>
   15702:	002a                	c.slli	zero,0xa
   15704:	0031                	c.nop	12
   15706:	001e                	c.slli	zero,0x7
   15708:	00f3ffcf          	fnmadd.s	ft11,ft7,fa5,ft0
   1570c:	0090                	addi	a2,sp,64
   1570e:	0015                	c.nop	5
   15710:	ff1c                	fsw	fa5,56(a4)
   15712:	ff84                	fsw	fs1,56(a5)
   15714:	ffb8                	fsw	fa4,120(a5)
   15716:	ffa0                	fsw	fs0,120(a5)
   15718:	ff42                	fsw	fa6,188(sp)
   1571a:	0049                	c.nop	18
   1571c:	ff51                	bnez	a4,156b8 <sig+0x368>
   1571e:	0048                	addi	a0,sp,4
   15720:	00c1                	addi	ra,ra,16
   15722:	009f 0032 ffc0      	0xffc00032009f
   15728:	007c                	addi	a5,sp,12
   1572a:	001a                	c.slli	zero,0x6
   1572c:	01bc                	addi	a5,sp,200
   1572e:	ff82                	fsw	ft0,252(sp)
   15730:	0004                	0x4
   15732:	ff4e                	fsw	fs3,188(sp)
   15734:	0072ff8b          	0x72ff8b
   15738:	00a9                	addi	ra,ra,10
   1573a:	0012                	c.slli	zero,0x4
   1573c:	ffc5                	bnez	a5,156f4 <sig+0x3a4>
   1573e:	00c9                	addi	ra,ra,18
   15740:	ff9e                	fsw	ft7,252(sp)
   15742:	0108                	addi	a0,sp,128
   15744:	0064                	addi	s1,sp,12
   15746:	0079                	c.nop	30
   15748:	ffc4                	fsw	fs1,60(a5)
   1574a:	ffdf 0064 ff86      	0xff860064ffdf
   15750:	0c15                	addi	s8,s8,5
   15752:	07b12b7b          	0x7b12b7b
   15756:	1edf 0dda 1a20      	0x1a200dda1edf
   1575c:	0cb8                	addi	a4,sp,600
   1575e:	06f02fc3          	fmadd.q	ft11,ft0,fa5,ft0,rdn
   15762:	0f35                	addi	t5,t5,13
   15764:	078d                	addi	a5,a5,3
   15766:	0bf1                	addi	s7,s7,28
   15768:	2d0103b7          	lui	t2,0x2d010
   1576c:	15b702cf          	0x15b702cf
   15770:	0a38                	addi	a4,sp,280
   15772:	1d3d                	addi	s10,s10,-17
   15774:	09d8                	addi	a4,sp,212
   15776:	10e4                	addi	s1,sp,108
   15778:	2458                	fld	fa4,136(s0)
   1577a:	1c81                	addi	s9,s9,-32
   1577c:	28df 12f9 201a      	0x201a12f928df
   15782:	1e491d97          	auipc	s11,0x1e491
   15786:	0cda1b97          	auipc	s7,0xcda1
   1578a:	1e81                	addi	t4,t4,-32
   1578c:	190f19f3          	csrrw	s3,0x190,t5
   15790:	1818                	addi	a4,sp,48
   15792:	1591                	addi	a1,a1,-28
   15794:	16f421eb          	0x16f421eb
   15798:	248b173f 22092c41 	0x22092c41248b173f
   157a0:	1f3203a7          	0x1f3203a7
   157a4:	1eec                	addi	a1,sp,892
   157a6:	2d450637          	lui	a2,0x2d450
   157aa:	16ff1f03          	lh	t5,367(t5) # ffc3f16f <__BSS_END__+0xffc2756b>
   157ae:	0bc8                	addi	a0,sp,468
   157b0:	2c66263b          	0x2c66263b
   157b4:	212a                	fld	ft2,136(sp)
   157b6:	1d72                	slli	s10,s10,0x3c
   157b8:	01b1                	addi	gp,gp,12
   157ba:	0d56                	slli	s10,s10,0x15
   157bc:	27ec                	fld	fa1,200(a5)
   157be:	1b90                	addi	a2,sp,496
   157c0:	14dc0c6b          	0x14dc0c6b
   157c4:	2a95                	jal	15938 <sig+0x5e8>
   157c6:	1e61                	addi	t3,t3,-8
   157c8:	0822                	slli	a6,a6,0x8
   157ca:	04a80f8b          	0x4a80f8b
   157ce:	213b2ecf          	fnmadd.s	ft9,fs6,fs3,ft4,rdn
   157d2:	2e9e                	fld	ft9,448(sp)
   157d4:	2fd20393          	addi	t2,tp,765 # 2fd <main-0xfd77>
   157d8:	2d82                	fld	fs11,0(sp)
   157da:	0f00                	addi	s0,sp,912
   157dc:	2854                	fld	fa3,144(s0)
   157de:	1b831117          	auipc	sp,0x1b831
   157e2:	0121                	addi	sp,sp,8
   157e4:	1148                	addi	a0,sp,164
   157e6:	01d9                	addi	gp,gp,22
   157e8:	25cc                	fld	fa1,136(a1)
   157ea:	1c3d                	addi	s8,s8,-17
   157ec:	1a06                	slli	s4,s4,0x21
   157ee:	0878                	addi	a4,sp,28
   157f0:	2ff9                	jal	15fce <hm+0x47e>
   157f2:	2098                	fld	fa4,0(s1)
   157f4:	1322                	slli	t1,t1,0x28
   157f6:	2869                	jal	15890 <sig+0x540>
   157f8:	19ba                	slli	s3,s3,0x2e
   157fa:	0c32                	slli	s8,s8,0xc
   157fc:	2b6d                	jal	15db6 <hm+0x266>
   157fe:	16c9                	addi	a3,a3,-14
   15800:	065e201b          	0x65e201b
   15804:	005d                	c.nop	23
   15806:	25d72323          	sw	t4,582(a4)
   1580a:	003a                	c.slli	zero,0xe
   1580c:	1fc2                	slli	t6,t6,0x30
   1580e:	0f81                	addi	t6,t6,0
   15810:	29a0                	fld	fs0,80(a1)
   15812:	1181                	addi	gp,gp,-32
   15814:	0dfd                	addi	s11,s11,31
   15816:	2ac2                	fld	fs5,16(sp)
   15818:	0d97206b          	0xd97206b
   1581c:	0a66                	slli	s4,s4,0x19
   1581e:	003d                	c.nop	15
   15820:	0bfd                	addi	s7,s7,31
   15822:	1bff                	0x1bff
   15824:	2c41                	jal	15ab4 <sig+0x764>
   15826:	2702                	fld	fa4,0(sp)
   15828:	2ba8                	fld	fa0,80(a5)
   1582a:	1ac5                	addi	s5,s5,-15
   1582c:	114d                	addi	sp,sp,-13
   1582e:	1210                	addi	a2,sp,288
   15830:	274c                	fld	fa1,136(a4)
   15832:	1386                	slli	t2,t2,0x21
   15834:	276a17b7          	lui	a5,0x276a1
   15838:	1491                	addi	s1,s1,-28
   1583a:	041a                	slli	s0,s0,0x6
   1583c:	1f910893          	addi	a7,sp,505 # 1b8469d7 <__BSS_END__+0x1b82edd3>
   15840:	1884                	addi	s1,sp,112
   15842:	1558                	addi	a4,sp,676
   15844:	2eaa                	fld	ft9,136(sp)
   15846:	04f1                	addi	s1,s1,28
   15848:	055a094f          	0x55a094f
   1584c:	1d2715c3          	0x1d2715c3
   15850:	2f81                	jal	15fa0 <hm+0x450>
   15852:	234d23a7          	fsw	fs4,551(s10)
   15856:	0b0d                	addi	s6,s6,3
   15858:	0c06                	slli	s8,s8,0x1
   1585a:	25f510f7          	0x25f510f7
   1585e:	0ce5                	addi	s9,s9,25
   15860:	245a                	fld	fs0,400(sp)
   15862:	1cdd                	addi	s9,s9,-9
   15864:	170617db          	0x170617db
   15868:	17ec                	addi	a1,sp,1004
   1586a:	2735                	jal	15f96 <hm+0x446>
   1586c:	1969                	addi	s2,s2,-6
   1586e:	1c14                	addi	a3,sp,560
   15870:	0206                	slli	tp,tp,0x1
   15872:	076b04eb          	0x76b04eb
   15876:	2b0415f7          	0x2b0415f7
   1587a:	150e2c43          	0x150e2c43
   1587e:	2b2c                	fld	fa1,80(a4)
   15880:	2721                	jal	15f88 <hm+0x438>
   15882:	253c                	fld	fa5,72(a0)
   15884:	2826                	fld	fa6,72(sp)
   15886:	0b8e                	slli	s7,s7,0x3
   15888:	200c0683          	lb	a3,512(s8)
   1588c:	25c5                	jal	15f6c <hm+0x41c>
   1588e:	29f2                	fld	fs3,280(sp)
   15890:	28f8                	fld	fa4,208(s1)
   15892:	0824                	addi	s1,sp,24
   15894:	05b613f3          	csrrw	t2,0x5b,a2
   15898:	223d                	jal	159c6 <sig+0x676>
   1589a:	17e4                	addi	s1,sp,1004
   1589c:	0c18209b          	0xc18209b
   158a0:	0d7002eb          	0xd7002eb
   158a4:	2a9a                	fld	fs5,384(sp)
   158a6:	0c3a091b          	0xc3a091b
   158aa:	1d450c27          	0x1d450c27
   158ae:	1830                	addi	a2,sp,56
   158b0:	279f0387          	0x279f0387
   158b4:	29af09cb          	fnmsub.s	fs3,ft10,fs10,ft5,rne
   158b8:	13f0                	addi	a2,sp,492
   158ba:	021a                	slli	tp,tp,0x6
   158bc:	28ba                	fld	fa7,392(sp)
   158be:	266a                	fld	fa2,152(sp)
   158c0:	265c                	fld	fa5,136(a2)
   158c2:	2080                	fld	fs0,0(s1)
   158c4:	0590                	addi	a2,sp,704
   158c6:	1955                	addi	s2,s2,-11
   158c8:	29ad                	jal	15d42 <hm+0x1f2>
   158ca:	0ea9                	addi	t4,t4,10
   158cc:	2211                	jal	159d0 <sig+0x680>
   158ce:	23c203b3          	0x23c203b3
   158d2:	0231                	addi	tp,tp,12
   158d4:	20f1                	jal	159a0 <sig+0x650>
   158d6:	220d                	jal	159f8 <sig+0x6a8>
   158d8:	1a9e02f7          	0x1a9e02f7
   158dc:	11a6                	slli	gp,gp,0x29
   158de:	1cb925b3          	0x1cb925b3
   158e2:	04b0                	addi	a2,sp,584
   158e4:	00c4                	addi	s1,sp,68
   158e6:	085c                	addi	a5,sp,20
   158e8:	2f1e                	fld	ft10,448(sp)
   158ea:	0672                	slli	a2,a2,0x1c
   158ec:	1558                	addi	a4,sp,676
   158ee:	29e4                	fld	fs1,208(a1)
   158f0:	2f14263f 284a178e 	0x284a178e2f14263f
   158f8:	2fdf 12a0 2982      	0x298212a02fdf
   158fe:	05e5                	addi	a1,a1,25
   15900:	2b32                	fld	fs6,264(sp)
   15902:	2f30                	fld	fa2,88(a4)
   15904:	2c20                	fld	fs0,88(s0)
   15906:	2d4e                	fld	fs10,208(sp)
   15908:	1a852997          	auipc	s3,0x1a852
   1590c:	1974                	addi	a3,sp,188
   1590e:	19b226f7          	0x19b226f7
   15912:	105e                	c.slli	zero,0x37
   15914:	0e4d09cf          	fnmadd.q	fs3,fs10,ft4,ft1,rne
   15918:	0420                	addi	s0,sp,520
   1591a:	0bd2                	slli	s7,s7,0x14
   1591c:	0945                	addi	s2,s2,17
   1591e:	0535                	addi	a0,a0,13
   15920:	0c15                	addi	s8,s8,5
   15922:	1a86                	slli	s5,s5,0x21
   15924:	20d5                	jal	15a08 <sig+0x6b8>
   15926:	04b51963          	bne	a0,a1,15978 <sig+0x628>
   1592a:	2d26                	fld	fs10,72(sp)
   1592c:	0a24                	addi	s1,sp,280
   1592e:	173e                	slli	a4,a4,0x2f
   15930:	061a                	slli	a2,a2,0x6
   15932:	2759236b          	0x2759236b
   15936:	183016ab          	0x183016ab
   1593a:	2f01                	jal	1604a <hm+0x4fa>
   1593c:	07b02ccf          	fnmadd.q	fs9,ft0,fs11,ft0,rdn
   15940:	19511a3b          	0x19511a3b
   15944:	0306                	slli	t1,t1,0x1
   15946:	17c0                	addi	s0,sp,996
   15948:	25a6                	fld	fa1,72(sp)
   1594a:	2805                	jal	1597a <sig+0x62a>
   1594c:	0aac                	addi	a1,sp,344
   1594e:	12e4                	addi	s1,sp,364
   15950:	00f20ed7          	0xf20ed7
   15954:	08b9                	addi	a7,a7,14
   15956:	253c0e87          	0x253c0e87
   1595a:	24fa                	fld	fs1,408(sp)
   1595c:	198e                	slli	s3,s3,0x23
   1595e:	21370a43          	fmadd.s	fs4,fa4,fs3,ft4,rne
   15962:	1c0c                	addi	a1,sp,560
   15964:	10be                	slli	ra,ra,0x2f
   15966:	227f0663          	beq	t5,t2,15b92 <hm+0x42>
   1596a:	0b2e                	slli	s6,s6,0xb
   1596c:	1cca                	slli	s9,s9,0x32
   1596e:	2c3d                	jal	15bac <hm+0x5c>
   15970:	07fd                	addi	a5,a5,31
   15972:	0c36                	slli	s8,s8,0xd
   15974:	09d2                	slli	s3,s3,0x14
   15976:	022d                	addi	tp,tp,11
   15978:	191d                	addi	s2,s2,-25
   1597a:	0c91                	addi	s9,s9,4
   1597c:	2d88                	fld	fa0,24(a1)
   1597e:	0b1c                	addi	a5,sp,400
   15980:	17d2229b          	0x17d2229b
   15984:	1c44                	addi	s1,sp,564
   15986:	0ffd                	addi	t6,t6,31
   15988:	1bd2                	slli	s7,s7,0x34
   1598a:	171c                	addi	a5,sp,928
   1598c:	28e42973          	csrrs	s2,0x28e,s0
   15990:	1972                	slli	s2,s2,0x3c
   15992:	0471                	addi	s0,s0,28
   15994:	1b6c0d6f          	jal	s10,d5b4a <__BSS_END__+0xbdf46>
   15998:	10a1                	addi	ra,ra,-24
   1599a:	18ad                	addi	a7,a7,-21
   1599c:	155d                	addi	a0,a0,-9
   1599e:	14e8                	addi	a0,sp,620
   159a0:	2831103f 0e3703f3 	0xe3703f32831103f
   159a8:	1f81                	addi	t6,t6,-32
   159aa:	1cc4                	addi	s1,sp,628
   159ac:	130a276b          	0x130a276b
   159b0:	1e48                	addi	a0,sp,820
   159b2:	2256280b          	0x2256280b
   159b6:	1208                	addi	a0,sp,288
   159b8:	0919                	addi	s2,s2,6
   159ba:	122e                	slli	tp,tp,0x2b
   159bc:	16c8                	addi	a0,sp,868
   159be:	2ee8                	fld	fa0,216(a3)
   159c0:	0212                	slli	tp,tp,0x4
   159c2:	0140                	addi	s0,sp,132
   159c4:	080c                	addi	a1,sp,16
   159c6:	1ff72f83          	lw	t6,511(a4)
   159ca:	0b0e                	slli	s6,s6,0x3
   159cc:	02a20d27          	0x2a20d27
   159d0:	17f2                	slli	a5,a5,0x3c
   159d2:	251f 1f83 220a      	0x220a1f83251f
   159d8:	19ee                	slli	s3,s3,0x3b
   159da:	2e34                	fld	fa3,88(a2)
   159dc:	23f91d77          	0x23f91d77
   159e0:	28b4                	fld	fa3,80(s1)
   159e2:	2542                	fld	fa0,16(sp)
   159e4:	0f56                	slli	t5,t5,0x15
   159e6:	2e29                	jal	15d00 <hm+0x1b0>
   159e8:	11a9                	addi	gp,gp,-22
   159ea:	08de                	slli	a7,a7,0x17
   159ec:	2f54                	fld	fa3,152(a4)
   159ee:	2b05                	jal	15f1e <hm+0x3ce>
   159f0:	207d                	jal	15a9e <sig+0x74e>
   159f2:	0a5e                	slli	s4,s4,0x17
   159f4:	2f66                	fld	ft10,88(sp)
   159f6:	1188                	addi	a0,sp,224
   159f8:	01f42a5b          	0x1f42a5b
   159fc:	105d                	c.nop	-9
   159fe:	1a491553          	fdiv.d	fa0,fs2,ft4,rtz
   15a02:	0845                	addi	a6,a6,17
   15a04:	10c4                	addi	s1,sp,100
   15a06:	0346                	slli	t1,t1,0x11
   15a08:	0fc5                	addi	t6,t6,17
   15a0a:	2464                	fld	fs1,200(s0)
   15a0c:	15e0                	addi	s0,sp,748
   15a0e:	14b4                	addi	a3,sp,616
   15a10:	01e42e73          	csrrs	t3,0x1e,s0
   15a14:	1d061c43          	0x1d061c43
   15a18:	17ad                	addi	a5,a5,-21
   15a1a:	0f9e                	slli	t6,t6,0x7
   15a1c:	0635                	addi	a2,a2,13
   15a1e:	18de                	slli	a7,a7,0x37
   15a20:	09ca                	slli	s3,s3,0x12
   15a22:	16e00687          	0x16e00687
   15a26:	2786                	fld	fa5,64(sp)
   15a28:	267e                	fld	fa2,472(sp)
   15a2a:	1f16                	slli	t5,t5,0x25
   15a2c:	26f1                	jal	15df8 <hm+0x2a8>
   15a2e:	090e                	slli	s2,s2,0x3
   15a30:	25640533          	0x25640533
   15a34:	1cfa                	slli	s9,s9,0x3e
   15a36:	17c9234f          	fnmadd.q	ft6,fs2,ft8,ft2,rdn
   15a3a:	11a6                	slli	gp,gp,0x29
   15a3c:	0be2                	slli	s7,s7,0x18
   15a3e:	2bc5                	jal	1602e <hm+0x4de>
   15a40:	14ce                	slli	s1,s1,0x33
   15a42:	2c0e                	fld	fs8,192(sp)
   15a44:	06de                	slli	a3,a3,0x17
   15a46:	2b24                	fld	fs1,80(a4)
   15a48:	0eae                	slli	t4,t4,0xb
   15a4a:	0c66                	slli	s8,s8,0x19
   15a4c:	2b75                	jal	16008 <hm+0x4b8>
   15a4e:	254a                	fld	fa0,144(sp)
   15a50:	0140                	addi	s0,sp,132
   15a52:	05b9                	addi	a1,a1,14
   15a54:	2b9209f3          	0x2b9209f3
   15a58:	2172                	fld	ft2,280(sp)
   15a5a:	058a                	slli	a1,a1,0x2
   15a5c:	2005                	jal	15a7c <sig+0x72c>
   15a5e:	112a                	slli	sp,sp,0x2a
   15a60:	2fb8                	fld	fa4,88(a5)
   15a62:	26f21467          	0x26f21467
   15a66:	0ddc                	addi	a5,sp,724
   15a68:	14c5                	addi	s1,s1,-15
   15a6a:	2dff                	0x2dff
   15a6c:	1358                	addi	a4,sp,420
   15a6e:	2af5                	jal	15c6a <hm+0x11a>
   15a70:	245f 1973 1ae5      	0x1ae51973245f
   15a76:	1ec8                	addi	a0,sp,884
   15a78:	212b1a63          	bne	s6,s2,15c8c <hm+0x13c>
   15a7c:	2bec                	fld	fa1,208(a5)
   15a7e:	20eb032b          	0x20eb032b
   15a82:	00fc                	addi	a5,sp,76
   15a84:	0bf6                	slli	s7,s7,0x1d
   15a86:	14e5                	addi	s1,s1,-7
   15a88:	2862                	fld	fa6,24(sp)
   15a8a:	0d1a                	slli	s10,s10,0x6
   15a8c:	1ee2                	slli	t4,t4,0x38
   15a8e:	17cc                	addi	a1,sp,996
   15a90:	0c35                	addi	s8,s8,13
   15a92:	2bd8283b          	0x2bd8283b
   15a96:	1dce                	slli	s11,s11,0x33
   15a98:	2c09                	jal	15caa <hm+0x15a>
   15a9a:	15ee                	slli	a1,a1,0x3b
   15a9c:	1045                	c.nop	-15
   15a9e:	1fb1                	addi	t6,t6,-20
   15aa0:	13e1                	addi	t2,t2,-8
   15aa2:	0aa11163          	bne	sp,a0,15b44 <sig+0x7f4>
   15aa6:	047f                	0x47f
   15aa8:	188320cf          	fnmadd.s	ft1,ft6,fs0,ft3,rdn
   15aac:	093d                	addi	s2,s2,15
   15aae:	2b9a                	fld	fs7,384(sp)
   15ab0:	2b6d                	jal	1606a <hm+0x51a>
   15ab2:	170e1faf          	0x170e1faf
   15ab6:	0961                	addi	s2,s2,24
   15ab8:	1c26                	slli	s8,s8,0x29
   15aba:	17e0                	addi	s0,sp,1004
   15abc:	2701                	jal	161bc <hm+0x66c>
   15abe:	052e                	slli	a0,a0,0xb
   15ac0:	0bb0                	addi	a2,sp,472
   15ac2:	2f5a                	fld	ft10,400(sp)
   15ac4:	0612                	slli	a2,a2,0x4
   15ac6:	19d9                	addi	s3,s3,-10
   15ac8:	13d2                	slli	t2,t2,0x34
   15aca:	226a                	fld	ft4,152(sp)
   15acc:	0d22                	slli	s10,s10,0x8
   15ace:	0c52                	slli	s8,s8,0x14
   15ad0:	2605                	jal	15df0 <hm+0x2a0>
   15ad2:	2cf2                	fld	fs9,280(sp)
   15ad4:	0d36                	slli	s10,s10,0xd
   15ad6:	1eca                	slli	t4,t4,0x32
   15ad8:	1cc22803          	lw	a6,460(tp) # 1cc <main-0xfea8>
   15adc:	105717cf          	fnmadd.s	fa5,fa4,ft5,ft2,rtz
   15ae0:	0e8d                	addi	t4,t4,3
   15ae2:	0011                	c.nop	4
   15ae4:	0232                	slli	tp,tp,0xc
   15ae6:	14942ff7          	0x14942ff7
   15aea:	0e8228bb          	0xe8228bb
   15aee:	1a65                	addi	s4,s4,-7
   15af0:	10c8                	addi	a0,sp,100
   15af2:	289c                	fld	fa5,16(s1)
   15af4:	0f99                	addi	t6,t6,6
   15af6:	2c96283b          	0x2c96283b
   15afa:	022e                	slli	tp,tp,0xb
   15afc:	275027eb          	0x275027eb
   15b00:	2bda01f3          	0x2bda01f3
   15b04:	29360873          	0x29360873
   15b08:	0e5e                	slli	t3,t3,0x17
   15b0a:	0124166f          	jal	a2,56b1c <__BSS_END__+0x3ef18>
   15b0e:	17962bc7          	fmsub.q	fs7,fa2,fs9,ft2,rdn
   15b12:	179a                	slli	a5,a5,0x26
   15b14:	0842                	slli	a6,a6,0x10
   15b16:	0750                	addi	a2,sp,900
   15b18:	0904                	addi	s1,sp,144
   15b1a:	0ca32b2f          	amoswap.w.aq	s6,a0,(t1)
   15b1e:	12ff                	0x12ff
   15b20:	0abc                	addi	a5,sp,344
   15b22:	06c2                	slli	a3,a3,0x10
   15b24:	13a0                	addi	s0,sp,488
   15b26:	2f0d                	jal	16258 <hm+0x708>
   15b28:	0914                	addi	a3,sp,144
   15b2a:	1b08                	addi	a0,sp,432
   15b2c:	204c                	fld	fa1,128(s0)
   15b2e:	2191                	jal	15f72 <hm+0x422>
   15b30:	133319f3          	csrrw	s3,0x133,t1
   15b34:	030d                	addi	t1,t1,3
   15b36:	198e1673          	csrrw	a2,0x198,t3
   15b3a:	0669                	addi	a2,a2,26
   15b3c:	11b6                	slli	gp,gp,0x2d
   15b3e:	06ce                	slli	a3,a3,0x13
   15b40:	2089                	jal	15b82 <hm+0x32>
   15b42:	11b1                	addi	gp,gp,-20
   15b44:	1ad5                	addi	s5,s5,-11
   15b46:	12d6                	slli	t0,t0,0x35
   15b48:	29a9                	jal	15fa2 <hm+0x452>
   15b4a:	2238                	fld	fa4,64(a2)
   15b4c:	00c1                	addi	ra,ra,16
   15b4e:	2ad2                	fld	fs5,272(sp)

00015b50 <hm>:
   15b50:	0c15                	addi	s8,s8,5
   15b52:	07b12b7b          	0x7b12b7b
   15b56:	1edf 0dda 1a20      	0x1a200dda1edf
   15b5c:	0cb8                	addi	a4,sp,600
   15b5e:	06f02fc3          	fmadd.q	ft11,ft0,fa5,ft0,rdn
   15b62:	0f35                	addi	t5,t5,13
   15b64:	078d                	addi	a5,a5,3
   15b66:	0bf1                	addi	s7,s7,28
   15b68:	2d0103b7          	lui	t2,0x2d010
   15b6c:	15b702cf          	0x15b702cf
   15b70:	0a38                	addi	a4,sp,280
   15b72:	1d3d                	addi	s10,s10,-17
   15b74:	09d8                	addi	a4,sp,212
   15b76:	10e4                	addi	s1,sp,108
   15b78:	2458                	fld	fa4,136(s0)
   15b7a:	1c81                	addi	s9,s9,-32
   15b7c:	28df 12f9 201a      	0x201a12f928df
   15b82:	1e491d97          	auipc	s11,0x1e491
   15b86:	0cda1b97          	auipc	s7,0xcda1
   15b8a:	1e81                	addi	t4,t4,-32
   15b8c:	190f19f3          	csrrw	s3,0x190,t5
   15b90:	1818                	addi	a4,sp,48
   15b92:	1591                	addi	a1,a1,-28
   15b94:	16f421eb          	0x16f421eb
   15b98:	248b173f 22092c41 	0x22092c41248b173f
   15ba0:	1f3203a7          	0x1f3203a7
   15ba4:	1eec                	addi	a1,sp,892
   15ba6:	2d450637          	lui	a2,0x2d450
   15baa:	16ff1f03          	lh	t5,367(t5)
   15bae:	0bc8                	addi	a0,sp,468
   15bb0:	2c66263b          	0x2c66263b
   15bb4:	212a                	fld	ft2,136(sp)
   15bb6:	1d72                	slli	s10,s10,0x3c
   15bb8:	01b1                	addi	gp,gp,12
   15bba:	0d56                	slli	s10,s10,0x15
   15bbc:	27ec                	fld	fa1,200(a5)
   15bbe:	1b90                	addi	a2,sp,496
   15bc0:	14dc0c6b          	0x14dc0c6b
   15bc4:	2a95                	jal	15d38 <hm+0x1e8>
   15bc6:	1e61                	addi	t3,t3,-8
   15bc8:	0822                	slli	a6,a6,0x8
   15bca:	04a80f8b          	0x4a80f8b
   15bce:	213b2ecf          	fnmadd.s	ft9,fs6,fs3,ft4,rdn
   15bd2:	2e9e                	fld	ft9,448(sp)
   15bd4:	2fd20393          	addi	t2,tp,765 # 2fd <main-0xfd77>
   15bd8:	2d82                	fld	fs11,0(sp)
   15bda:	0f00                	addi	s0,sp,912
   15bdc:	2854                	fld	fa3,144(s0)
   15bde:	1b831117          	auipc	sp,0x1b831
   15be2:	0121                	addi	sp,sp,8
   15be4:	1148                	addi	a0,sp,164
   15be6:	01d9                	addi	gp,gp,22
   15be8:	25cc                	fld	fa1,136(a1)
   15bea:	1c3d                	addi	s8,s8,-17
   15bec:	1a06                	slli	s4,s4,0x21
   15bee:	0878                	addi	a4,sp,28
   15bf0:	2ff9                	jal	163ce <hm+0x87e>
   15bf2:	2098                	fld	fa4,0(s1)
   15bf4:	1322                	slli	t1,t1,0x28
   15bf6:	2869                	jal	15c90 <hm+0x140>
   15bf8:	19ba                	slli	s3,s3,0x2e
   15bfa:	0c32                	slli	s8,s8,0xc
   15bfc:	2b6d                	jal	161b6 <hm+0x666>
   15bfe:	16c9                	addi	a3,a3,-14
   15c00:	065e201b          	0x65e201b
   15c04:	005d                	c.nop	23
   15c06:	25d72323          	sw	t4,582(a4)
   15c0a:	003a                	c.slli	zero,0xe
   15c0c:	1fc2                	slli	t6,t6,0x30
   15c0e:	0f81                	addi	t6,t6,0
   15c10:	29a0                	fld	fs0,80(a1)
   15c12:	1181                	addi	gp,gp,-32
   15c14:	0dfd                	addi	s11,s11,31
   15c16:	2ac2                	fld	fs5,16(sp)
   15c18:	0d97206b          	0xd97206b
   15c1c:	0a66                	slli	s4,s4,0x19
   15c1e:	003d                	c.nop	15
   15c20:	0bfd                	addi	s7,s7,31
   15c22:	1bff                	0x1bff
   15c24:	2c41                	jal	15eb4 <hm+0x364>
   15c26:	2702                	fld	fa4,0(sp)
   15c28:	2ba8                	fld	fa0,80(a5)
   15c2a:	1ac5                	addi	s5,s5,-15
   15c2c:	114d                	addi	sp,sp,-13
   15c2e:	1210                	addi	a2,sp,288
   15c30:	274c                	fld	fa1,136(a4)
   15c32:	1386                	slli	t2,t2,0x21
   15c34:	276a17b7          	lui	a5,0x276a1
   15c38:	1491                	addi	s1,s1,-28
   15c3a:	041a                	slli	s0,s0,0x6
   15c3c:	1f910893          	addi	a7,sp,505 # 1b846dd7 <__BSS_END__+0x1b82f1d3>
   15c40:	1884                	addi	s1,sp,112
   15c42:	1558                	addi	a4,sp,676
   15c44:	2eaa                	fld	ft9,136(sp)
   15c46:	04f1                	addi	s1,s1,28
   15c48:	055a094f          	0x55a094f
   15c4c:	1d2715c3          	0x1d2715c3
   15c50:	2f81                	jal	163a0 <hm+0x850>
   15c52:	234d23a7          	fsw	fs4,551(s10)
   15c56:	0b0d                	addi	s6,s6,3
   15c58:	0c06                	slli	s8,s8,0x1
   15c5a:	25f510f7          	0x25f510f7
   15c5e:	0ce5                	addi	s9,s9,25
   15c60:	245a                	fld	fs0,400(sp)
   15c62:	1cdd                	addi	s9,s9,-9
   15c64:	170617db          	0x170617db
   15c68:	17ec                	addi	a1,sp,1004
   15c6a:	2735                	jal	16396 <hm+0x846>
   15c6c:	1969                	addi	s2,s2,-6
   15c6e:	1c14                	addi	a3,sp,560
   15c70:	0206                	slli	tp,tp,0x1
   15c72:	076b04eb          	0x76b04eb
   15c76:	2b0415f7          	0x2b0415f7
   15c7a:	150e2c43          	0x150e2c43
   15c7e:	2b2c                	fld	fa1,80(a4)
   15c80:	2721                	jal	16388 <hm+0x838>
   15c82:	253c                	fld	fa5,72(a0)
   15c84:	2826                	fld	fa6,72(sp)
   15c86:	0b8e                	slli	s7,s7,0x3
   15c88:	200c0683          	lb	a3,512(s8)
   15c8c:	25c5                	jal	1636c <hm+0x81c>
   15c8e:	29f2                	fld	fs3,280(sp)
   15c90:	28f8                	fld	fa4,208(s1)
   15c92:	0824                	addi	s1,sp,24
   15c94:	05b613f3          	csrrw	t2,0x5b,a2
   15c98:	223d                	jal	15dc6 <hm+0x276>
   15c9a:	17e4                	addi	s1,sp,1004
   15c9c:	0c18209b          	0xc18209b
   15ca0:	0d7002eb          	0xd7002eb
   15ca4:	2a9a                	fld	fs5,384(sp)
   15ca6:	0c3a091b          	0xc3a091b
   15caa:	1d450c27          	0x1d450c27
   15cae:	1830                	addi	a2,sp,56
   15cb0:	279f0387          	0x279f0387
   15cb4:	29af09cb          	fnmsub.s	fs3,ft10,fs10,ft5,rne
   15cb8:	13f0                	addi	a2,sp,492
   15cba:	021a                	slli	tp,tp,0x6
   15cbc:	28ba                	fld	fa7,392(sp)
   15cbe:	266a                	fld	fa2,152(sp)
   15cc0:	265c                	fld	fa5,136(a2)
   15cc2:	2080                	fld	fs0,0(s1)
   15cc4:	0590                	addi	a2,sp,704
   15cc6:	1955                	addi	s2,s2,-11
   15cc8:	29ad                	jal	16142 <hm+0x5f2>
   15cca:	0ea9                	addi	t4,t4,10
   15ccc:	2211                	jal	15dd0 <hm+0x280>
   15cce:	23c203b3          	0x23c203b3
   15cd2:	0231                	addi	tp,tp,12
   15cd4:	20f1                	jal	15da0 <hm+0x250>
   15cd6:	220d                	jal	15df8 <hm+0x2a8>
   15cd8:	1a9e02f7          	0x1a9e02f7
   15cdc:	11a6                	slli	gp,gp,0x29
   15cde:	1cb925b3          	0x1cb925b3
   15ce2:	04b0                	addi	a2,sp,584
   15ce4:	00c4                	addi	s1,sp,68
   15ce6:	085c                	addi	a5,sp,20
   15ce8:	2f1e                	fld	ft10,448(sp)
   15cea:	0672                	slli	a2,a2,0x1c
   15cec:	1558                	addi	a4,sp,676
   15cee:	29e4                	fld	fs1,208(a1)
   15cf0:	2f14263f 284a178e 	0x284a178e2f14263f
   15cf8:	2fdf 12a0 2982      	0x298212a02fdf
   15cfe:	05e5                	addi	a1,a1,25
   15d00:	2b32                	fld	fs6,264(sp)
   15d02:	2f30                	fld	fa2,88(a4)
   15d04:	2c20                	fld	fs0,88(s0)
   15d06:	2d4e                	fld	fs10,208(sp)
   15d08:	1a852997          	auipc	s3,0x1a852
   15d0c:	1974                	addi	a3,sp,188
   15d0e:	19b226f7          	0x19b226f7
   15d12:	105e                	c.slli	zero,0x37
   15d14:	0e4d09cf          	fnmadd.q	fs3,fs10,ft4,ft1,rne
   15d18:	0420                	addi	s0,sp,520
   15d1a:	0bd2                	slli	s7,s7,0x14
   15d1c:	0945                	addi	s2,s2,17
   15d1e:	0535                	addi	a0,a0,13
   15d20:	0c15                	addi	s8,s8,5
   15d22:	1a86                	slli	s5,s5,0x21
   15d24:	20d5                	jal	15e08 <hm+0x2b8>
   15d26:	04b51963          	bne	a0,a1,15d78 <hm+0x228>
   15d2a:	2d26                	fld	fs10,72(sp)
   15d2c:	0a24                	addi	s1,sp,280
   15d2e:	173e                	slli	a4,a4,0x2f
   15d30:	061a                	slli	a2,a2,0x6
   15d32:	2759236b          	0x2759236b
   15d36:	183016ab          	0x183016ab
   15d3a:	2f01                	jal	1644a <hm+0x8fa>
   15d3c:	07b02ccf          	fnmadd.q	fs9,ft0,fs11,ft0,rdn
   15d40:	19511a3b          	0x19511a3b
   15d44:	0306                	slli	t1,t1,0x1
   15d46:	17c0                	addi	s0,sp,996
   15d48:	25a6                	fld	fa1,72(sp)
   15d4a:	2805                	jal	15d7a <hm+0x22a>
   15d4c:	0aac                	addi	a1,sp,344
   15d4e:	12e4                	addi	s1,sp,364
   15d50:	00f20ed7          	0xf20ed7
   15d54:	08b9                	addi	a7,a7,14
   15d56:	253c0e87          	0x253c0e87
   15d5a:	24fa                	fld	fs1,408(sp)
   15d5c:	198e                	slli	s3,s3,0x23
   15d5e:	21370a43          	fmadd.s	fs4,fa4,fs3,ft4,rne
   15d62:	1c0c                	addi	a1,sp,560
   15d64:	10be                	slli	ra,ra,0x2f
   15d66:	227f0663          	beq	t5,t2,15f92 <hm+0x442>
   15d6a:	0b2e                	slli	s6,s6,0xb
   15d6c:	1cca                	slli	s9,s9,0x32
   15d6e:	2c3d                	jal	15fac <hm+0x45c>
   15d70:	07fd                	addi	a5,a5,31
   15d72:	0c36                	slli	s8,s8,0xd
   15d74:	09d2                	slli	s3,s3,0x14
   15d76:	022d                	addi	tp,tp,11
   15d78:	191d                	addi	s2,s2,-25
   15d7a:	0c91                	addi	s9,s9,4
   15d7c:	2d88                	fld	fa0,24(a1)
   15d7e:	0b1c                	addi	a5,sp,400
   15d80:	17d2229b          	0x17d2229b
   15d84:	1c44                	addi	s1,sp,564
   15d86:	0ffd                	addi	t6,t6,31
   15d88:	1bd2                	slli	s7,s7,0x34
   15d8a:	171c                	addi	a5,sp,928
   15d8c:	28e42973          	csrrs	s2,0x28e,s0
   15d90:	1972                	slli	s2,s2,0x3c
   15d92:	0471                	addi	s0,s0,28
   15d94:	1b6c0d6f          	jal	s10,d5f4a <__BSS_END__+0xbe346>
   15d98:	10a1                	addi	ra,ra,-24
   15d9a:	18ad                	addi	a7,a7,-21
   15d9c:	155d                	addi	a0,a0,-9
   15d9e:	14e8                	addi	a0,sp,620
   15da0:	2831103f 0e3703f3 	0xe3703f32831103f
   15da8:	1f81                	addi	t6,t6,-32
   15daa:	1cc4                	addi	s1,sp,628
   15dac:	130a276b          	0x130a276b
   15db0:	1e48                	addi	a0,sp,820
   15db2:	2256280b          	0x2256280b
   15db6:	1208                	addi	a0,sp,288
   15db8:	0919                	addi	s2,s2,6
   15dba:	122e                	slli	tp,tp,0x2b
   15dbc:	16c8                	addi	a0,sp,868
   15dbe:	2ee8                	fld	fa0,216(a3)
   15dc0:	0212                	slli	tp,tp,0x4
   15dc2:	0140                	addi	s0,sp,132
   15dc4:	080c                	addi	a1,sp,16
   15dc6:	1ff72f83          	lw	t6,511(a4)
   15dca:	0b0e                	slli	s6,s6,0x3
   15dcc:	02a20d27          	0x2a20d27
   15dd0:	17f2                	slli	a5,a5,0x3c
   15dd2:	251f 1f83 220a      	0x220a1f83251f
   15dd8:	19ee                	slli	s3,s3,0x3b
   15dda:	2e34                	fld	fa3,88(a2)
   15ddc:	23f91d77          	0x23f91d77
   15de0:	28b4                	fld	fa3,80(s1)
   15de2:	2542                	fld	fa0,16(sp)
   15de4:	0f56                	slli	t5,t5,0x15
   15de6:	2e29                	jal	16100 <hm+0x5b0>
   15de8:	11a9                	addi	gp,gp,-22
   15dea:	08de                	slli	a7,a7,0x17
   15dec:	2f54                	fld	fa3,152(a4)
   15dee:	2b05                	jal	1631e <hm+0x7ce>
   15df0:	207d                	jal	15e9e <hm+0x34e>
   15df2:	0a5e                	slli	s4,s4,0x17
   15df4:	2f66                	fld	ft10,88(sp)
   15df6:	1188                	addi	a0,sp,224
   15df8:	01f42a5b          	0x1f42a5b
   15dfc:	105d                	c.nop	-9
   15dfe:	1a491553          	fdiv.d	fa0,fs2,ft4,rtz
   15e02:	0845                	addi	a6,a6,17
   15e04:	10c4                	addi	s1,sp,100
   15e06:	0346                	slli	t1,t1,0x11
   15e08:	0fc5                	addi	t6,t6,17
   15e0a:	2464                	fld	fs1,200(s0)
   15e0c:	15e0                	addi	s0,sp,748
   15e0e:	14b4                	addi	a3,sp,616
   15e10:	01e42e73          	csrrs	t3,0x1e,s0
   15e14:	1d061c43          	0x1d061c43
   15e18:	17ad                	addi	a5,a5,-21
   15e1a:	0f9e                	slli	t6,t6,0x7
   15e1c:	0635                	addi	a2,a2,13
   15e1e:	18de                	slli	a7,a7,0x37
   15e20:	09ca                	slli	s3,s3,0x12
   15e22:	16e00687          	0x16e00687
   15e26:	2786                	fld	fa5,64(sp)
   15e28:	267e                	fld	fa2,472(sp)
   15e2a:	1f16                	slli	t5,t5,0x25
   15e2c:	26f1                	jal	161f8 <hm+0x6a8>
   15e2e:	090e                	slli	s2,s2,0x3
   15e30:	25640533          	0x25640533
   15e34:	1cfa                	slli	s9,s9,0x3e
   15e36:	17c9234f          	fnmadd.q	ft6,fs2,ft8,ft2,rdn
   15e3a:	11a6                	slli	gp,gp,0x29
   15e3c:	0be2                	slli	s7,s7,0x18
   15e3e:	2bc5                	jal	1642e <hm+0x8de>
   15e40:	14ce                	slli	s1,s1,0x33
   15e42:	2c0e                	fld	fs8,192(sp)
   15e44:	06de                	slli	a3,a3,0x17
   15e46:	2b24                	fld	fs1,80(a4)
   15e48:	0eae                	slli	t4,t4,0xb
   15e4a:	0c66                	slli	s8,s8,0x19
   15e4c:	2b75                	jal	16408 <hm+0x8b8>
   15e4e:	254a                	fld	fa0,144(sp)
   15e50:	0140                	addi	s0,sp,132
   15e52:	05b9                	addi	a1,a1,14
   15e54:	2b9209f3          	0x2b9209f3
   15e58:	2172                	fld	ft2,280(sp)
   15e5a:	058a                	slli	a1,a1,0x2
   15e5c:	2005                	jal	15e7c <hm+0x32c>
   15e5e:	112a                	slli	sp,sp,0x2a
   15e60:	2fb8                	fld	fa4,88(a5)
   15e62:	26f21467          	0x26f21467
   15e66:	0ddc                	addi	a5,sp,724
   15e68:	14c5                	addi	s1,s1,-15
   15e6a:	2dff                	0x2dff
   15e6c:	1358                	addi	a4,sp,420
   15e6e:	2af5                	jal	1606a <hm+0x51a>
   15e70:	245f 1973 1ae5      	0x1ae51973245f
   15e76:	1ec8                	addi	a0,sp,884
   15e78:	212b1a63          	bne	s6,s2,1608c <hm+0x53c>
   15e7c:	2bec                	fld	fa1,208(a5)
   15e7e:	20eb032b          	0x20eb032b
   15e82:	00fc                	addi	a5,sp,76
   15e84:	0bf6                	slli	s7,s7,0x1d
   15e86:	14e5                	addi	s1,s1,-7
   15e88:	2862                	fld	fa6,24(sp)
   15e8a:	0d1a                	slli	s10,s10,0x6
   15e8c:	1ee2                	slli	t4,t4,0x38
   15e8e:	17cc                	addi	a1,sp,996
   15e90:	0c35                	addi	s8,s8,13
   15e92:	2bd8283b          	0x2bd8283b
   15e96:	1dce                	slli	s11,s11,0x33
   15e98:	2c09                	jal	160aa <hm+0x55a>
   15e9a:	15ee                	slli	a1,a1,0x3b
   15e9c:	1045                	c.nop	-15
   15e9e:	1fb1                	addi	t6,t6,-20
   15ea0:	13e1                	addi	t2,t2,-8
   15ea2:	0aa11163          	bne	sp,a0,15f44 <hm+0x3f4>
   15ea6:	047f                	0x47f
   15ea8:	188320cf          	fnmadd.s	ft1,ft6,fs0,ft3,rdn
   15eac:	093d                	addi	s2,s2,15
   15eae:	2b9a                	fld	fs7,384(sp)
   15eb0:	2b6d                	jal	1646a <hm+0x91a>
   15eb2:	170e1faf          	0x170e1faf
   15eb6:	0961                	addi	s2,s2,24
   15eb8:	1c26                	slli	s8,s8,0x29
   15eba:	17e0                	addi	s0,sp,1004
   15ebc:	2701                	jal	165bc <hm+0xa6c>
   15ebe:	052e                	slli	a0,a0,0xb
   15ec0:	0bb0                	addi	a2,sp,472
   15ec2:	2f5a                	fld	ft10,400(sp)
   15ec4:	0612                	slli	a2,a2,0x4
   15ec6:	19d9                	addi	s3,s3,-10
   15ec8:	13d2                	slli	t2,t2,0x34
   15eca:	226a                	fld	ft4,152(sp)
   15ecc:	0d22                	slli	s10,s10,0x8
   15ece:	0c52                	slli	s8,s8,0x14
   15ed0:	2605                	jal	161f0 <hm+0x6a0>
   15ed2:	2cf2                	fld	fs9,280(sp)
   15ed4:	0d36                	slli	s10,s10,0xd
   15ed6:	1eca                	slli	t4,t4,0x32
   15ed8:	1cc22803          	lw	a6,460(tp) # 1cc <main-0xfea8>
   15edc:	105717cf          	fnmadd.s	fa5,fa4,ft5,ft2,rtz
   15ee0:	0e8d                	addi	t4,t4,3
   15ee2:	0011                	c.nop	4
   15ee4:	0232                	slli	tp,tp,0xc
   15ee6:	14942ff7          	0x14942ff7
   15eea:	0e8228bb          	0xe8228bb
   15eee:	1a65                	addi	s4,s4,-7
   15ef0:	10c8                	addi	a0,sp,100
   15ef2:	289c                	fld	fa5,16(s1)
   15ef4:	0f99                	addi	t6,t6,6
   15ef6:	2c96283b          	0x2c96283b
   15efa:	022e                	slli	tp,tp,0xb
   15efc:	275027eb          	0x275027eb
   15f00:	2bda01f3          	0x2bda01f3
   15f04:	29360873          	0x29360873
   15f08:	0e5e                	slli	t3,t3,0x17
   15f0a:	0124166f          	jal	a2,56f1c <__BSS_END__+0x3f318>
   15f0e:	17962bc7          	fmsub.q	fs7,fa2,fs9,ft2,rdn
   15f12:	179a                	slli	a5,a5,0x26
   15f14:	0842                	slli	a6,a6,0x10
   15f16:	0750                	addi	a2,sp,900
   15f18:	0904                	addi	s1,sp,144
   15f1a:	0ca32b2f          	amoswap.w.aq	s6,a0,(t1)
   15f1e:	12ff                	0x12ff
   15f20:	0abc                	addi	a5,sp,344
   15f22:	06c2                	slli	a3,a3,0x10
   15f24:	13a0                	addi	s0,sp,488
   15f26:	2f0d                	jal	16658 <hm+0xb08>
   15f28:	0914                	addi	a3,sp,144
   15f2a:	1b08                	addi	a0,sp,432
   15f2c:	204c                	fld	fa1,128(s0)
   15f2e:	2191                	jal	16372 <hm+0x822>
   15f30:	133319f3          	csrrw	s3,0x133,t1
   15f34:	030d                	addi	t1,t1,3
   15f36:	198e1673          	csrrw	a2,0x198,t3
   15f3a:	0669                	addi	a2,a2,26
   15f3c:	11b6                	slli	gp,gp,0x2d
   15f3e:	06ce                	slli	a3,a3,0x13
   15f40:	2089                	jal	15f82 <hm+0x432>
   15f42:	11b1                	addi	gp,gp,-20
   15f44:	1ad5                	addi	s5,s5,-11
   15f46:	12d6                	slli	t0,t0,0x35
   15f48:	29a9                	jal	163a2 <hm+0x852>
   15f4a:	2238                	fld	fa4,64(a2)
   15f4c:	00c1                	addi	ra,ra,16
   15f4e:	2ad2                	fld	fs5,272(sp)
   15f50:	2db0                	fld	fa2,88(a1)
   15f52:	24cf2767          	0x24cf2767
   15f56:	1ef2200f          	0x1ef2200f
   15f5a:	0059                	c.nop	22
   15f5c:	148f0d3f 07640bb2 	0x7640bb2148f0d3f
   15f64:	0754                	addi	a3,sp,900
   15f66:	2a74                	fld	fa3,208(a2)
   15f68:	251a                	fld	fa0,384(sp)
   15f6a:	2532                	fld	fa0,264(sp)
   15f6c:	0edc09e7          	jalr	s3,237(s8)
   15f70:	14c8                	addi	a0,sp,612
   15f72:	0d70                	addi	a2,sp,668
   15f74:	0405                	addi	s0,s0,1
   15f76:	2ba9                	jal	164d0 <hm+0x980>
   15f78:	14f9                	addi	s1,s1,-2
   15f7a:	11d2                	slli	gp,gp,0x34
   15f7c:	2596                	fld	fa1,320(sp)
   15f7e:	27d8                	fld	fa4,136(a5)
   15f80:	2470                	fld	fa2,200(s0)
   15f82:	2e0a                	fld	ft8,128(sp)
   15f84:	1b28                	addi	a0,sp,440
   15f86:	0059                	c.nop	22
   15f88:	2b1e2ac7          	fmsub.d	fs5,ft8,fa7,ft5,rdn
   15f8c:	162a                	slli	a2,a2,0x2a
   15f8e:	2b2e                	fld	fs6,200(sp)
   15f90:	0212                	slli	tp,tp,0x4
   15f92:	239e                	fld	ft7,448(sp)
   15f94:	20da09d7          	0x20da09d7
   15f98:	1a15                	addi	s4,s4,-27
   15f9a:	19ab07eb          	0x19ab07eb
   15f9e:	0561                	addi	a0,a0,24
   15fa0:	2b5e2a63          	0x2b5e2a63
   15fa4:	2f78                	fld	fa4,216(a4)
   15fa6:	0f4a                	slli	t5,t5,0x12
   15fa8:	0c4a                	slli	s8,s8,0x12
   15faa:	2442                	fld	fs0,16(sp)
   15fac:	0f1e                	slli	t5,t5,0x7
   15fae:	1d42                	slli	s10,s10,0x30
   15fb0:	1749                	addi	a4,a4,-14
   15fb2:	0a56                	slli	s4,s4,0x15
   15fb4:	07cc                	addi	a1,sp,964
   15fb6:	1eaa                	slli	t4,t4,0x2a
   15fb8:	1dad                	addi	s11,s11,-21
   15fba:	28b4                	fld	fa3,80(s1)
   15fbc:	1482                	slli	s1,s1,0x20
   15fbe:	2734                	fld	fa3,72(a4)
   15fc0:	0044                	addi	s1,sp,4
   15fc2:	26bc                	fld	fa5,72(a3)
   15fc4:	0d1a                	slli	s10,s10,0x6
   15fc6:	2b1d                	jal	164fc <hm+0x9ac>
   15fc8:	081f 1653 085c      	0x85c1653081f
   15fce:	272329bf 178c0e47 	0x178c0e47272329bf
   15fd6:	28b101a3          	sb	a1,643(sp)
   15fda:	285e0d2f          	0x285e0d2f
   15fde:	0e7f16e3          	bne	t5,t2,168ca <hm+0xd7a>
   15fe2:	1506                	slli	a0,a0,0x21
   15fe4:	2295                	jal	16148 <hm+0x5f8>
   15fe6:	2c4c                	fld	fa1,152(s0)
   15fe8:	2a24                	fld	fs1,80(a2)
   15fea:	2e02080f          	0x2e02080f
   15fee:	11c92957          	0x11c92957
   15ff2:	03c8                	addi	a0,sp,452
   15ff4:	2275                	jal	161a0 <hm+0x650>
   15ff6:	1898                	addi	a4,sp,112
   15ff8:	048c0897          	auipc	a7,0x48c0
   15ffc:	1d18                	addi	a4,sp,688
   15ffe:	1d84                	addi	s1,sp,752
   16000:	0fcd                	addi	t6,t6,19
   16002:	185603b7          	lui	t2,0x18560
   16006:	06c22af3          	csrrs	s5,0x6c,tp
   1600a:	04700e63          	beq	zero,t2,16066 <hm+0x516>
   1600e:	2338                	fld	fa4,64(a4)
   16010:	215e                	fld	ft2,464(sp)
   16012:	06e8                	addi	a0,sp,844
   16014:	28ce                	fld	fa7,208(sp)
   16016:	02df 1e7c 21f9      	0x21f91e7c02df
   1601c:	11b9                	addi	gp,gp,-18
   1601e:	2224                	fld	fs1,64(a2)
   16020:	2051                	jal	160a4 <hm+0x554>
   16022:	22c407e7          	jalr	a5,556(s0)
   16026:	126d                	addi	tp,tp,-5
   16028:	2205                	jal	16148 <hm+0x5f8>
   1602a:	2e65                	jal	163e2 <hm+0x892>
   1602c:	0dec                	addi	a1,sp,732
   1602e:	17d6                	slli	a5,a5,0x35
   16030:	1b5a                	slli	s6,s6,0x36
   16032:	185a                	slli	a6,a6,0x36
   16034:	18aa                	slli	a7,a7,0x2a
   16036:	0c9d                	addi	s9,s9,7
   16038:	08fc                	addi	a5,sp,92
   1603a:	1015                	c.nop	-27
   1603c:	2e8a                	fld	ft9,128(sp)
   1603e:	03bc1af3          	csrrw	s5,0x3b,s8
   16042:	1afc0a0f          	0x1afc0a0f
   16046:	2b95                	jal	165ba <hm+0xa6a>
   16048:	2538                	fld	fa4,72(a0)
   1604a:	0462                	slli	s0,s0,0x18
   1604c:	1453038f          	0x1453038f
   16050:	1cfc12fb          	0x1cfc12fb
   16054:	03d2                	slli	t2,t2,0x14
   16056:	0aad                	addi	s5,s5,11
   16058:	0be1                	addi	s7,s7,24
   1605a:	1e94                	addi	a3,sp,880
   1605c:	25881763          	bne	a6,s8,162aa <hm+0x75a>
   16060:	096c                	addi	a1,sp,156
   16062:	0ffc                	addi	a5,sp,988
   16064:	257a                	fld	fa0,408(sp)
   16066:	066d                	addi	a2,a2,27
   16068:	1dda01cf          	0x1dda01cf
   1606c:	2b1e                	fld	fs6,448(sp)
   1606e:	101d                	c.nop	-25
   16070:	0728                	addi	a0,sp,904
   16072:	2da2                	fld	fs11,8(sp)
   16074:	1cbe                	slli	s9,s9,0x2f
   16076:	2ab82423          	sw	a1,680(a6)
   1607a:	21da                	fld	ft3,400(sp)
   1607c:	26b9                	jal	163ca <hm+0x87a>
   1607e:	07ed                	addi	a5,a5,27
   16080:	0ab8                	addi	a4,sp,344
   16082:	141d                	addi	s0,s0,-25
   16084:	0fee                	slli	t6,t6,0x1b
   16086:	062c                	addi	a1,sp,776
   16088:	15d2                	slli	a1,a1,0x34
   1608a:	24a2                	fld	fs1,8(sp)
   1608c:	049d                	addi	s1,s1,7
   1608e:	0ece                	slli	t4,t4,0x13
   16090:	116e                	slli	sp,sp,0x3b
   16092:	04b607a7          	0x4b607a7
   16096:	116d                	addi	sp,sp,-5
   16098:	031f 0367 12cf      	0x12cf0367031f
   1609e:	29e6                	fld	fs3,88(sp)
   160a0:	2e14                	fld	fa3,24(a2)
   160a2:	107e                	c.slli	zero,0x3f
   160a4:	2134                	fld	fa3,64(a0)
   160a6:	018e                	slli	gp,gp,0x3
   160a8:	05b9                	addi	a1,a1,14
   160aa:	1358                	addi	a4,sp,420
   160ac:	26cc                	fld	fa1,136(a3)
   160ae:	078d220f          	0x78d220f
   160b2:	1950                	addi	a2,sp,180
   160b4:	2612                	fld	fa2,256(sp)
   160b6:	041f 116b 2b41      	0x2b41116b041f
   160bc:	1e30                	addi	a2,sp,824
   160be:	22f4                	fld	fa3,192(a3)
   160c0:	0898                	addi	a4,sp,80
   160c2:	261c                	fld	fa5,8(a2)
   160c4:	11371a3b          	0x11371a3b
   160c8:	1e5d0b67          	jalr	s6,485(s10)
   160cc:	2ad1                	jal	162a0 <hm+0x750>
   160ce:	0dcc                	addi	a1,sp,724
   160d0:	23b4                	fld	fa3,64(a5)
   160d2:	0079                	c.nop	30
   160d4:	2901                	jal	164e4 <hm+0x994>
   160d6:	2951                	jal	1656a <hm+0xa1a>
   160d8:	1ee8                	addi	a0,sp,892
   160da:	293a                	fld	fs2,392(sp)
   160dc:	11a0                	addi	s0,sp,232
   160de:	1ac0                	addi	s0,sp,372
   160e0:	21c2                	fld	ft3,16(sp)
   160e2:	2bcc                	fld	fa1,144(a5)
   160e4:	20e1                	jal	161ac <hm+0x65c>
   160e6:	2cde29c3          	0x2cde29c3
   160ea:	0bc6                	slli	s7,s7,0x11
   160ec:	2195                	jal	16550 <hm+0xa00>
   160ee:	2ce9                	jal	163c8 <hm+0x878>
   160f0:	21b5                	jal	1655c <hm+0xa0c>
   160f2:	00cd                	addi	ra,ra,19
   160f4:	1d26                	slli	s10,s10,0x29
   160f6:	0c80                	addi	s0,sp,592
   160f8:	1c79                	addi	s8,s8,-2
   160fa:	2e78066b          	0x2e78066b
   160fe:	0c94                	addi	a3,sp,592
   16100:	2874                	fld	fa3,208(s0)
   16102:	1321                	addi	t1,t1,-24
   16104:	10f70bd7          	0x10f70bd7
   16108:	1d65                	addi	s10,s10,-7
   1610a:	2db6                	fld	fs11,328(sp)
   1610c:	2e58                	fld	fa4,152(a2)
   1610e:	0bd016ab          	0xbd016ab
   16112:	2acd                	jal	16304 <hm+0x7b4>
   16114:	22c4                	fld	fs1,128(a3)
   16116:	0f51                	addi	t5,t5,20
   16118:	2ce8                	fld	fa0,216(s1)
   1611a:	1e5f2d1b          	0x1e5f2d1b
   1611e:	01fa                	slli	gp,gp,0x1e
   16120:	29010be7          	jalr	s7,656(sp)
   16124:	1051                	c.nop	-12
   16126:	0d0e                	slli	s10,s10,0x3
   16128:	2d20282f          	0x2d20282f
   1612c:	1342                	slli	t1,t1,0x30
   1612e:	2a49                	jal	162c0 <hm+0x770>
   16130:	1aa2                	slli	s5,s5,0x28
   16132:	2fd5                	jal	16926 <hm+0xdd6>
   16134:	1db2                	slli	s11,s11,0x2c
   16136:	1f34                	addi	a3,sp,952
   16138:	2a51098b          	0x2a51098b
   1613c:	20cc                	fld	fa1,128(s1)
   1613e:	238b1977          	0x238b1977
   16142:	06fc14b7          	lui	s1,0x6fc1
   16146:	16702fcf          	fnmadd.q	ft11,ft0,ft7,ft2,rdn
   1614a:	07c0                	addi	s0,sp,964
   1614c:	2600                	fld	fs0,8(a2)
   1614e:	100c18a7          	0x100c18a7
   16152:	168625cb          	fnmsub.q	fa1,fa2,fs0,ft2,rdn
   16156:	2465                	jal	163fe <hm+0x8ae>
   16158:	23ba2f17          	auipc	t5,0x23ba2
   1615c:	2d5f 208c 1e0b      	0x1e0b208c2d5f
   16162:	1e40                	addi	s0,sp,820
   16164:	04df 0843 17c5      	0x17c5084304df
   1616a:	1fdd                	addi	t6,t6,-9
   1616c:	2dbc                	fld	fa5,88(a1)
   1616e:	1f88                	addi	a0,sp,1008
   16170:	029d                	addi	t0,t0,7
   16172:	0311                	addi	t1,t1,4
   16174:	1e45                	addi	t3,t3,-15
   16176:	0701                	addi	a4,a4,0
   16178:	1751                	addi	a4,a4,-12
   1617a:	11ac                	addi	a1,sp,232
   1617c:	2f35                	jal	168b8 <hm+0xd68>
   1617e:	236c                	fld	fa1,192(a4)
   16180:	042a                	slli	s0,s0,0xa
   16182:	14f50543          	0x14f50543
   16186:	2120                	fld	fs0,64(a0)
   16188:	1ad2                	slli	s5,s5,0x34
   1618a:	0239                	addi	tp,tp,14
   1618c:	0009                	c.nop	2
   1618e:	1ab4                	addi	a3,sp,376
   16190:	1202                	slli	tp,tp,0x20
   16192:	135a198f          	0x135a198f
   16196:	1081                	addi	ra,ra,-32
   16198:	21fc                	fld	fa5,192(a1)
   1619a:	0979                	addi	s2,s2,30
   1619c:	2e95                	jal	16510 <hm+0x9c0>
   1619e:	239a                	fld	ft7,384(sp)
   161a0:	0888                	addi	a0,sp,80
   161a2:	20e42c07          	flw	fs8,526(s0)
   161a6:	012a                	slli	sp,sp,0xa
   161a8:	0d65                	addi	s10,s10,25
   161aa:	0551                	addi	a0,a0,20
   161ac:	03c5                	addi	t2,t2,17
   161ae:	02800667          	jalr	a2,40(zero) # 0 <main-0x10074>
   161b2:	0059                	c.nop	22
   161b4:	14ba                	slli	s1,s1,0x2e
   161b6:	1b5c2b07          	flw	fs6,437(s8)
   161ba:	201d                	jal	161e0 <hm+0x690>
   161bc:	2cd92daf          	0x2cd92daf
   161c0:	2111                	jal	165c4 <hm+0xa74>
   161c2:	29ce                	fld	fs3,208(sp)
   161c4:	0791                	addi	a5,a5,4
   161c6:	2644                	fld	fs1,136(a2)
   161c8:	2ecd                	jal	165ba <hm+0xa6a>
   161ca:	1acb2d67          	0x1acb2d67
   161ce:	0489                	addi	s1,s1,2
   161d0:	12b4                	addi	a3,sp,360
   161d2:	28ae                	fld	fa7,200(sp)
   161d4:	1a2d                	addi	s4,s4,-21
   161d6:	2e42                	fld	ft8,16(sp)
   161d8:	258b0c47          	0x258b0c47
   161dc:	1258                	addi	a4,sp,292
   161de:	05fd                	addi	a1,a1,31
   161e0:	2aec                	fld	fa1,208(a3)
   161e2:	010c                	addi	a1,sp,128
   161e4:	292e                	fld	fs2,200(sp)
   161e6:	1631                	addi	a2,a2,-20
   161e8:	23d1                	jal	167ac <hm+0xc5c>
   161ea:	06c1                	addi	a3,a3,16
   161ec:	0c18                	addi	a4,sp,528
   161ee:	1df2                	slli	s11,s11,0x3c
   161f0:	1a3513ef          	jal	t2,67b92 <__BSS_END__+0x4ff8e>
   161f4:	1ec1                	addi	t4,t4,-16
   161f6:	118d                	addi	gp,gp,-29
   161f8:	0c60                	addi	s0,sp,540
   161fa:	25f0                	fld	fa2,200(a1)
   161fc:	0cb5                	addi	s9,s9,13
   161fe:	0d99                	addi	s11,s11,6
   16200:	2679                	jal	1658e <hm+0xa3e>
   16202:	2d55                	jal	168b6 <hm+0xd66>
   16204:	2b55                	jal	167b8 <hm+0xc68>
   16206:	10060b97          	auipc	s7,0x10060
   1620a:	24f8                	fld	fa4,200(s1)
   1620c:	2cd8                	fld	fa4,152(s1)
   1620e:	21942f27          	fsw	fs9,542(s0)
   16212:	298c194b          	fnmsub.s	fs2,fs8,fs8,ft5,rtz
   16216:	03be                	slli	t2,t2,0xf
   16218:	256a                	fld	fa0,152(sp)
   1621a:	2c85                	jal	1648a <hm+0x93a>
   1621c:	1d55                	addi	s10,s10,-11
   1621e:	1766                	slli	a4,a4,0x39
   16220:	1ed5                	addi	t4,t4,-11
   16222:	1d020393          	addi	t2,tp,464 # 1d0 <main-0xfea4>
   16226:	19bc0757          	0x19bc0757
   1622a:	0c920f8b          	0xc920f8b
   1622e:	10b1                	addi	ra,ra,-20
   16230:	2f6c                	fld	fa1,216(a4)
   16232:	2334                	fld	fa3,64(a4)
   16234:	0e19                	addi	t3,t3,6
   16236:	2835274b          	fnmsub.s	fa4,fa0,ft3,ft5,rdn
   1623a:	22c02abb          	0x22c02abb
   1623e:	1dc6                	slli	s11,s11,0x31
   16240:	1bc4                	addi	s1,sp,500
   16242:	0a4e                	slli	s4,s4,0x13
   16244:	23e5                	jal	1682c <hm+0xcdc>
   16246:	05cd                	addi	a1,a1,19
   16248:	2b84                	fld	fs1,16(a5)
   1624a:	18960807          	0x18960807
   1624e:	2b90025b          	0x2b90025b
   16252:	1ab1                	addi	s5,s5,-20
   16254:	2e10                	fld	fa2,24(a2)
   16256:	1d7d                	addi	s10,s10,-1
   16258:	092206f3          	0x92206f3
   1625c:	21f4                	fld	fa3,192(a1)
   1625e:	2f6e                	fld	ft10,216(sp)
   16260:	29ae                	fld	fs3,200(sp)
   16262:	122310bb          	0x122310bb
   16266:	13422a5b          	0x13422a5b
   1626a:	03d9                	addi	t2,t2,22
   1626c:	1b5b04af          	0x1b5b04af
   16270:	1570                	addi	a2,sp,684
   16272:	15dc                	addi	a5,sp,740
   16274:	01c6                	slli	gp,gp,0x11
   16276:	2146                	fld	ft2,80(sp)
   16278:	0b3c                	addi	a5,sp,408
   1627a:	10f9                	addi	ra,ra,-2
   1627c:	053d                	addi	a0,a0,15
   1627e:	2762                	fld	fa4,24(sp)
   16280:	0071                	c.nop	28
   16282:	1bcd                	addi	s7,s7,-13
   16284:	2cee                	fld	fs9,216(sp)
   16286:	05b50f6b          	0x5b50f6b
   1628a:	1d7a                	slli	s10,s10,0x3e
   1628c:	1408028f          	0x1408028f
   16290:	2569232b          	0x2569232b
   16294:	12bd                	addi	t0,t0,-17
   16296:	2b0c                	fld	fa1,16(a4)
   16298:	0a6a1cab          	0xa6a1cab
   1629c:	1ef2                	slli	t4,t4,0x3c
   1629e:	1a6a                	slli	s4,s4,0x3a
   162a0:	0c0e                	slli	s8,s8,0x3
   162a2:	27a32efb          	0x27a32efb
   162a6:	00c9                	addi	ra,ra,18
   162a8:	1fea                	slli	t6,t6,0x3a
   162aa:	1898                	addi	a4,sp,112
   162ac:	2bb0                	fld	fa2,80(a5)
   162ae:	19262703          	lw	a4,402(a2) # 2d450192 <__BSS_END__+0x2d43858e>
   162b2:	06532d3b          	0x6532d3b
   162b6:	2442                	fld	fs0,16(sp)
   162b8:	13aa                	slli	t2,t2,0x2a
   162ba:	05af2137          	lui	sp,0x5af2
   162be:	0d94                	addi	a3,sp,720
   162c0:	211413e3          	bne	s0,a7,16cc6 <hm+0x1176>
   162c4:	2279                	jal	16452 <hm+0x902>
   162c6:	2329                	jal	167d0 <hm+0xc80>
   162c8:	2f4e                	fld	ft10,208(sp)
   162ca:	1369                	addi	t1,t1,-6
   162cc:	12de                	slli	t0,t0,0x37
   162ce:	01e2                	slli	gp,gp,0x18
   162d0:	0c850157          	0xc850157
   162d4:	2eac                	fld	fa1,88(a3)
   162d6:	15631957          	0x15631957
   162da:	0108                	addi	a0,sp,128
   162dc:	1dc206b7          	lui	a3,0x1dc20
   162e0:	218d                	jal	16742 <hm+0xbf2>
   162e2:	01c9                	addi	gp,gp,18
   162e4:	0b6b2ac7          	fmsub.d	fs5,fs6,fs6,ft1,rdn
   162e8:	18ce                	slli	a7,a7,0x33
   162ea:	12da                	slli	t0,t0,0x36
   162ec:	018c                	addi	a1,sp,192
   162ee:	0b75                	addi	s6,s6,29
   162f0:	03c9                	addi	t2,t2,18
   162f2:	18d4                	addi	a3,sp,116
   162f4:	06bc                	addi	a5,sp,840
   162f6:	2a52                	fld	fs4,272(sp)
   162f8:	2d1a                	fld	fs10,384(sp)
   162fa:	0882160f          	0x882160f
   162fe:	24c1                	jal	165be <hm+0xa6e>
   16300:	2ac0                	fld	fs0,144(a3)
   16302:	0d61                	addi	s10,s10,24
   16304:	1cb2                	slli	s9,s9,0x2c
   16306:	08492a2f          	amoswap.w	s4,tp,(s2)
   1630a:	0a940547          	fmsub.d	fa0,fs0,fs1,ft1,rne
   1630e:	1182                	slli	gp,gp,0x20
   16310:	0031                	c.nop	12
   16312:	2b38                	fld	fa4,80(a4)
   16314:	1ca0                	addi	s0,sp,632
   16316:	12ee0ab3          	0x12ee0ab3
   1631a:	0988                	addi	a0,sp,208
   1631c:	03b0                	addi	a2,sp,456
   1631e:	0ee4                	addi	s1,sp,860
   16320:	1aff                	0x1aff
   16322:	0205                	addi	tp,tp,1
   16324:	0801                	addi	a6,a6,0
   16326:	1ac1                	addi	s5,s5,-16
   16328:	0e5e                	slli	t3,t3,0x17
   1632a:	2739                	jal	16a38 <hm+0xee8>
   1632c:	13a1                	addi	t2,t2,-24
   1632e:	015c                	addi	a5,sp,132
   16330:	0f9e                	slli	t6,t6,0x7
   16332:	1d56                	slli	s10,s10,0x35
   16334:	0111                	addi	sp,sp,4
   16336:	2594                	fld	fa3,8(a1)
   16338:	21ef1623          	sh	t5,524(t5) # 23bb8364 <__BSS_END__+0x23ba0760>
   1633c:	2452                	fld	fs0,272(sp)
   1633e:	0819                	addi	a6,a6,6
   16340:	2528                	fld	fa0,72(a0)
   16342:	2c3c                	fld	fa5,88(s0)
   16344:	1a82                	slli	s5,s5,0x20
   16346:	15e6                	slli	a1,a1,0x39
   16348:	28bd                	jal	163c6 <hm+0x876>
   1634a:	2856                	fld	fa6,336(sp)
   1634c:	2bc607ab          	0x2bc607ab
   16350:	000a                	c.slli	zero,0x2

Disassembly of section .eh_frame:

00017354 <__FRAME_END__>:
   17354:	0000                	unimp
	...

Disassembly of section .init_array:

00017358 <__init_array_start>:
   17358:	00e4                	addi	s1,sp,76
   1735a:	0001                	nop

0001735c <__frame_dummy_init_array_entry>:
   1735c:	0190                	addi	a2,sp,192
   1735e:	0001                	nop

Disassembly of section .fini_array:

00017360 <__do_global_dtors_aux_fini_array_entry>:
   17360:	0148                	addi	a0,sp,132
   17362:	0001                	nop

Disassembly of section .data:

00017368 <impure_data>:
   17368:	0000                	unimp
   1736a:	0000                	unimp
   1736c:	7654                	flw	fa3,44(a2)
   1736e:	0001                	nop
   17370:	76bc                	flw	fa5,104(a3)
   17372:	0001                	nop
   17374:	7724                	flw	fs1,104(a4)
   17376:	0001                	nop
	...
   17410:	0001                	nop
   17412:	0000                	unimp
   17414:	0000                	unimp
   17416:	0000                	unimp
   17418:	330e                	fld	ft6,224(sp)
   1741a:	abcd                	j	17a0c <__malloc_av_+0x27c>
   1741c:	1234                	addi	a3,sp,296
   1741e:	e66d                	bnez	a2,17508 <impure_data+0x1a0>
   17420:	deec                	sw	a1,124(a3)
   17422:	0005                	c.nop	1
   17424:	0000000b          	0xb
	...

00017790 <__malloc_av_>:
	...
   17798:	7790                	flw	fa2,40(a5)
   1779a:	0001                	nop
   1779c:	7790                	flw	fa2,40(a5)
   1779e:	0001                	nop
   177a0:	7798                	flw	fa4,40(a5)
   177a2:	0001                	nop
   177a4:	7798                	flw	fa4,40(a5)
   177a6:	0001                	nop
   177a8:	77a0                	flw	fs0,104(a5)
   177aa:	0001                	nop
   177ac:	77a0                	flw	fs0,104(a5)
   177ae:	0001                	nop
   177b0:	77a8                	flw	fa0,104(a5)
   177b2:	0001                	nop
   177b4:	77a8                	flw	fa0,104(a5)
   177b6:	0001                	nop
   177b8:	77b0                	flw	fa2,104(a5)
   177ba:	0001                	nop
   177bc:	77b0                	flw	fa2,104(a5)
   177be:	0001                	nop
   177c0:	77b8                	flw	fa4,104(a5)
   177c2:	0001                	nop
   177c4:	77b8                	flw	fa4,104(a5)
   177c6:	0001                	nop
   177c8:	77c0                	flw	fs0,44(a5)
   177ca:	0001                	nop
   177cc:	77c0                	flw	fs0,44(a5)
   177ce:	0001                	nop
   177d0:	77c8                	flw	fa0,44(a5)
   177d2:	0001                	nop
   177d4:	77c8                	flw	fa0,44(a5)
   177d6:	0001                	nop
   177d8:	77d0                	flw	fa2,44(a5)
   177da:	0001                	nop
   177dc:	77d0                	flw	fa2,44(a5)
   177de:	0001                	nop
   177e0:	77d8                	flw	fa4,44(a5)
   177e2:	0001                	nop
   177e4:	77d8                	flw	fa4,44(a5)
   177e6:	0001                	nop
   177e8:	77e0                	flw	fs0,108(a5)
   177ea:	0001                	nop
   177ec:	77e0                	flw	fs0,108(a5)
   177ee:	0001                	nop
   177f0:	77e8                	flw	fa0,108(a5)
   177f2:	0001                	nop
   177f4:	77e8                	flw	fa0,108(a5)
   177f6:	0001                	nop
   177f8:	77f0                	flw	fa2,108(a5)
   177fa:	0001                	nop
   177fc:	77f0                	flw	fa2,108(a5)
   177fe:	0001                	nop
   17800:	77f8                	flw	fa4,108(a5)
   17802:	0001                	nop
   17804:	77f8                	flw	fa4,108(a5)
   17806:	0001                	nop
   17808:	7800                	flw	fs0,48(s0)
   1780a:	0001                	nop
   1780c:	7800                	flw	fs0,48(s0)
   1780e:	0001                	nop
   17810:	7808                	flw	fa0,48(s0)
   17812:	0001                	nop
   17814:	7808                	flw	fa0,48(s0)
   17816:	0001                	nop
   17818:	7810                	flw	fa2,48(s0)
   1781a:	0001                	nop
   1781c:	7810                	flw	fa2,48(s0)
   1781e:	0001                	nop
   17820:	7818                	flw	fa4,48(s0)
   17822:	0001                	nop
   17824:	7818                	flw	fa4,48(s0)
   17826:	0001                	nop
   17828:	7820                	flw	fs0,112(s0)
   1782a:	0001                	nop
   1782c:	7820                	flw	fs0,112(s0)
   1782e:	0001                	nop
   17830:	7828                	flw	fa0,112(s0)
   17832:	0001                	nop
   17834:	7828                	flw	fa0,112(s0)
   17836:	0001                	nop
   17838:	7830                	flw	fa2,112(s0)
   1783a:	0001                	nop
   1783c:	7830                	flw	fa2,112(s0)
   1783e:	0001                	nop
   17840:	7838                	flw	fa4,112(s0)
   17842:	0001                	nop
   17844:	7838                	flw	fa4,112(s0)
   17846:	0001                	nop
   17848:	7840                	flw	fs0,52(s0)
   1784a:	0001                	nop
   1784c:	7840                	flw	fs0,52(s0)
   1784e:	0001                	nop
   17850:	7848                	flw	fa0,52(s0)
   17852:	0001                	nop
   17854:	7848                	flw	fa0,52(s0)
   17856:	0001                	nop
   17858:	7850                	flw	fa2,52(s0)
   1785a:	0001                	nop
   1785c:	7850                	flw	fa2,52(s0)
   1785e:	0001                	nop
   17860:	7858                	flw	fa4,52(s0)
   17862:	0001                	nop
   17864:	7858                	flw	fa4,52(s0)
   17866:	0001                	nop
   17868:	7860                	flw	fs0,116(s0)
   1786a:	0001                	nop
   1786c:	7860                	flw	fs0,116(s0)
   1786e:	0001                	nop
   17870:	7868                	flw	fa0,116(s0)
   17872:	0001                	nop
   17874:	7868                	flw	fa0,116(s0)
   17876:	0001                	nop
   17878:	7870                	flw	fa2,116(s0)
   1787a:	0001                	nop
   1787c:	7870                	flw	fa2,116(s0)
   1787e:	0001                	nop
   17880:	7878                	flw	fa4,116(s0)
   17882:	0001                	nop
   17884:	7878                	flw	fa4,116(s0)
   17886:	0001                	nop
   17888:	7880                	flw	fs0,48(s1)
   1788a:	0001                	nop
   1788c:	7880                	flw	fs0,48(s1)
   1788e:	0001                	nop
   17890:	7888                	flw	fa0,48(s1)
   17892:	0001                	nop
   17894:	7888                	flw	fa0,48(s1)
   17896:	0001                	nop
   17898:	7890                	flw	fa2,48(s1)
   1789a:	0001                	nop
   1789c:	7890                	flw	fa2,48(s1)
   1789e:	0001                	nop
   178a0:	7898                	flw	fa4,48(s1)
   178a2:	0001                	nop
   178a4:	7898                	flw	fa4,48(s1)
   178a6:	0001                	nop
   178a8:	78a0                	flw	fs0,112(s1)
   178aa:	0001                	nop
   178ac:	78a0                	flw	fs0,112(s1)
   178ae:	0001                	nop
   178b0:	78a8                	flw	fa0,112(s1)
   178b2:	0001                	nop
   178b4:	78a8                	flw	fa0,112(s1)
   178b6:	0001                	nop
   178b8:	78b0                	flw	fa2,112(s1)
   178ba:	0001                	nop
   178bc:	78b0                	flw	fa2,112(s1)
   178be:	0001                	nop
   178c0:	78b8                	flw	fa4,112(s1)
   178c2:	0001                	nop
   178c4:	78b8                	flw	fa4,112(s1)
   178c6:	0001                	nop
   178c8:	78c0                	flw	fs0,52(s1)
   178ca:	0001                	nop
   178cc:	78c0                	flw	fs0,52(s1)
   178ce:	0001                	nop
   178d0:	78c8                	flw	fa0,52(s1)
   178d2:	0001                	nop
   178d4:	78c8                	flw	fa0,52(s1)
   178d6:	0001                	nop
   178d8:	78d0                	flw	fa2,52(s1)
   178da:	0001                	nop
   178dc:	78d0                	flw	fa2,52(s1)
   178de:	0001                	nop
   178e0:	78d8                	flw	fa4,52(s1)
   178e2:	0001                	nop
   178e4:	78d8                	flw	fa4,52(s1)
   178e6:	0001                	nop
   178e8:	78e0                	flw	fs0,116(s1)
   178ea:	0001                	nop
   178ec:	78e0                	flw	fs0,116(s1)
   178ee:	0001                	nop
   178f0:	78e8                	flw	fa0,116(s1)
   178f2:	0001                	nop
   178f4:	78e8                	flw	fa0,116(s1)
   178f6:	0001                	nop
   178f8:	78f0                	flw	fa2,116(s1)
   178fa:	0001                	nop
   178fc:	78f0                	flw	fa2,116(s1)
   178fe:	0001                	nop
   17900:	78f8                	flw	fa4,116(s1)
   17902:	0001                	nop
   17904:	78f8                	flw	fa4,116(s1)
   17906:	0001                	nop
   17908:	7900                	flw	fs0,48(a0)
   1790a:	0001                	nop
   1790c:	7900                	flw	fs0,48(a0)
   1790e:	0001                	nop
   17910:	7908                	flw	fa0,48(a0)
   17912:	0001                	nop
   17914:	7908                	flw	fa0,48(a0)
   17916:	0001                	nop
   17918:	7910                	flw	fa2,48(a0)
   1791a:	0001                	nop
   1791c:	7910                	flw	fa2,48(a0)
   1791e:	0001                	nop
   17920:	7918                	flw	fa4,48(a0)
   17922:	0001                	nop
   17924:	7918                	flw	fa4,48(a0)
   17926:	0001                	nop
   17928:	7920                	flw	fs0,112(a0)
   1792a:	0001                	nop
   1792c:	7920                	flw	fs0,112(a0)
   1792e:	0001                	nop
   17930:	7928                	flw	fa0,112(a0)
   17932:	0001                	nop
   17934:	7928                	flw	fa0,112(a0)
   17936:	0001                	nop
   17938:	7930                	flw	fa2,112(a0)
   1793a:	0001                	nop
   1793c:	7930                	flw	fa2,112(a0)
   1793e:	0001                	nop
   17940:	7938                	flw	fa4,112(a0)
   17942:	0001                	nop
   17944:	7938                	flw	fa4,112(a0)
   17946:	0001                	nop
   17948:	7940                	flw	fs0,52(a0)
   1794a:	0001                	nop
   1794c:	7940                	flw	fs0,52(a0)
   1794e:	0001                	nop
   17950:	7948                	flw	fa0,52(a0)
   17952:	0001                	nop
   17954:	7948                	flw	fa0,52(a0)
   17956:	0001                	nop
   17958:	7950                	flw	fa2,52(a0)
   1795a:	0001                	nop
   1795c:	7950                	flw	fa2,52(a0)
   1795e:	0001                	nop
   17960:	7958                	flw	fa4,52(a0)
   17962:	0001                	nop
   17964:	7958                	flw	fa4,52(a0)
   17966:	0001                	nop
   17968:	7960                	flw	fs0,116(a0)
   1796a:	0001                	nop
   1796c:	7960                	flw	fs0,116(a0)
   1796e:	0001                	nop
   17970:	7968                	flw	fa0,116(a0)
   17972:	0001                	nop
   17974:	7968                	flw	fa0,116(a0)
   17976:	0001                	nop
   17978:	7970                	flw	fa2,116(a0)
   1797a:	0001                	nop
   1797c:	7970                	flw	fa2,116(a0)
   1797e:	0001                	nop
   17980:	7978                	flw	fa4,116(a0)
   17982:	0001                	nop
   17984:	7978                	flw	fa4,116(a0)
   17986:	0001                	nop
   17988:	7980                	flw	fs0,48(a1)
   1798a:	0001                	nop
   1798c:	7980                	flw	fs0,48(a1)
   1798e:	0001                	nop
   17990:	7988                	flw	fa0,48(a1)
   17992:	0001                	nop
   17994:	7988                	flw	fa0,48(a1)
   17996:	0001                	nop
   17998:	7990                	flw	fa2,48(a1)
   1799a:	0001                	nop
   1799c:	7990                	flw	fa2,48(a1)
   1799e:	0001                	nop
   179a0:	7998                	flw	fa4,48(a1)
   179a2:	0001                	nop
   179a4:	7998                	flw	fa4,48(a1)
   179a6:	0001                	nop
   179a8:	79a0                	flw	fs0,112(a1)
   179aa:	0001                	nop
   179ac:	79a0                	flw	fs0,112(a1)
   179ae:	0001                	nop
   179b0:	79a8                	flw	fa0,112(a1)
   179b2:	0001                	nop
   179b4:	79a8                	flw	fa0,112(a1)
   179b6:	0001                	nop
   179b8:	79b0                	flw	fa2,112(a1)
   179ba:	0001                	nop
   179bc:	79b0                	flw	fa2,112(a1)
   179be:	0001                	nop
   179c0:	79b8                	flw	fa4,112(a1)
   179c2:	0001                	nop
   179c4:	79b8                	flw	fa4,112(a1)
   179c6:	0001                	nop
   179c8:	79c0                	flw	fs0,52(a1)
   179ca:	0001                	nop
   179cc:	79c0                	flw	fs0,52(a1)
   179ce:	0001                	nop
   179d0:	79c8                	flw	fa0,52(a1)
   179d2:	0001                	nop
   179d4:	79c8                	flw	fa0,52(a1)
   179d6:	0001                	nop
   179d8:	79d0                	flw	fa2,52(a1)
   179da:	0001                	nop
   179dc:	79d0                	flw	fa2,52(a1)
   179de:	0001                	nop
   179e0:	79d8                	flw	fa4,52(a1)
   179e2:	0001                	nop
   179e4:	79d8                	flw	fa4,52(a1)
   179e6:	0001                	nop
   179e8:	79e0                	flw	fs0,116(a1)
   179ea:	0001                	nop
   179ec:	79e0                	flw	fs0,116(a1)
   179ee:	0001                	nop
   179f0:	79e8                	flw	fa0,116(a1)
   179f2:	0001                	nop
   179f4:	79e8                	flw	fa0,116(a1)
   179f6:	0001                	nop
   179f8:	79f0                	flw	fa2,116(a1)
   179fa:	0001                	nop
   179fc:	79f0                	flw	fa2,116(a1)
   179fe:	0001                	nop
   17a00:	79f8                	flw	fa4,116(a1)
   17a02:	0001                	nop
   17a04:	79f8                	flw	fa4,116(a1)
   17a06:	0001                	nop
   17a08:	7a00                	flw	fs0,48(a2)
   17a0a:	0001                	nop
   17a0c:	7a00                	flw	fs0,48(a2)
   17a0e:	0001                	nop
   17a10:	7a08                	flw	fa0,48(a2)
   17a12:	0001                	nop
   17a14:	7a08                	flw	fa0,48(a2)
   17a16:	0001                	nop
   17a18:	7a10                	flw	fa2,48(a2)
   17a1a:	0001                	nop
   17a1c:	7a10                	flw	fa2,48(a2)
   17a1e:	0001                	nop
   17a20:	7a18                	flw	fa4,48(a2)
   17a22:	0001                	nop
   17a24:	7a18                	flw	fa4,48(a2)
   17a26:	0001                	nop
   17a28:	7a20                	flw	fs0,112(a2)
   17a2a:	0001                	nop
   17a2c:	7a20                	flw	fs0,112(a2)
   17a2e:	0001                	nop
   17a30:	7a28                	flw	fa0,112(a2)
   17a32:	0001                	nop
   17a34:	7a28                	flw	fa0,112(a2)
   17a36:	0001                	nop
   17a38:	7a30                	flw	fa2,112(a2)
   17a3a:	0001                	nop
   17a3c:	7a30                	flw	fa2,112(a2)
   17a3e:	0001                	nop
   17a40:	7a38                	flw	fa4,112(a2)
   17a42:	0001                	nop
   17a44:	7a38                	flw	fa4,112(a2)
   17a46:	0001                	nop
   17a48:	7a40                	flw	fs0,52(a2)
   17a4a:	0001                	nop
   17a4c:	7a40                	flw	fs0,52(a2)
   17a4e:	0001                	nop
   17a50:	7a48                	flw	fa0,52(a2)
   17a52:	0001                	nop
   17a54:	7a48                	flw	fa0,52(a2)
   17a56:	0001                	nop
   17a58:	7a50                	flw	fa2,52(a2)
   17a5a:	0001                	nop
   17a5c:	7a50                	flw	fa2,52(a2)
   17a5e:	0001                	nop
   17a60:	7a58                	flw	fa4,52(a2)
   17a62:	0001                	nop
   17a64:	7a58                	flw	fa4,52(a2)
   17a66:	0001                	nop
   17a68:	7a60                	flw	fs0,116(a2)
   17a6a:	0001                	nop
   17a6c:	7a60                	flw	fs0,116(a2)
   17a6e:	0001                	nop
   17a70:	7a68                	flw	fa0,116(a2)
   17a72:	0001                	nop
   17a74:	7a68                	flw	fa0,116(a2)
   17a76:	0001                	nop
   17a78:	7a70                	flw	fa2,116(a2)
   17a7a:	0001                	nop
   17a7c:	7a70                	flw	fa2,116(a2)
   17a7e:	0001                	nop
   17a80:	7a78                	flw	fa4,116(a2)
   17a82:	0001                	nop
   17a84:	7a78                	flw	fa4,116(a2)
   17a86:	0001                	nop
   17a88:	7a80                	flw	fs0,48(a3)
   17a8a:	0001                	nop
   17a8c:	7a80                	flw	fs0,48(a3)
   17a8e:	0001                	nop
   17a90:	7a88                	flw	fa0,48(a3)
   17a92:	0001                	nop
   17a94:	7a88                	flw	fa0,48(a3)
   17a96:	0001                	nop
   17a98:	7a90                	flw	fa2,48(a3)
   17a9a:	0001                	nop
   17a9c:	7a90                	flw	fa2,48(a3)
   17a9e:	0001                	nop
   17aa0:	7a98                	flw	fa4,48(a3)
   17aa2:	0001                	nop
   17aa4:	7a98                	flw	fa4,48(a3)
   17aa6:	0001                	nop
   17aa8:	7aa0                	flw	fs0,112(a3)
   17aaa:	0001                	nop
   17aac:	7aa0                	flw	fs0,112(a3)
   17aae:	0001                	nop
   17ab0:	7aa8                	flw	fa0,112(a3)
   17ab2:	0001                	nop
   17ab4:	7aa8                	flw	fa0,112(a3)
   17ab6:	0001                	nop
   17ab8:	7ab0                	flw	fa2,112(a3)
   17aba:	0001                	nop
   17abc:	7ab0                	flw	fa2,112(a3)
   17abe:	0001                	nop
   17ac0:	7ab8                	flw	fa4,112(a3)
   17ac2:	0001                	nop
   17ac4:	7ab8                	flw	fa4,112(a3)
   17ac6:	0001                	nop
   17ac8:	7ac0                	flw	fs0,52(a3)
   17aca:	0001                	nop
   17acc:	7ac0                	flw	fs0,52(a3)
   17ace:	0001                	nop
   17ad0:	7ac8                	flw	fa0,52(a3)
   17ad2:	0001                	nop
   17ad4:	7ac8                	flw	fa0,52(a3)
   17ad6:	0001                	nop
   17ad8:	7ad0                	flw	fa2,52(a3)
   17ada:	0001                	nop
   17adc:	7ad0                	flw	fa2,52(a3)
   17ade:	0001                	nop
   17ae0:	7ad8                	flw	fa4,52(a3)
   17ae2:	0001                	nop
   17ae4:	7ad8                	flw	fa4,52(a3)
   17ae6:	0001                	nop
   17ae8:	7ae0                	flw	fs0,116(a3)
   17aea:	0001                	nop
   17aec:	7ae0                	flw	fs0,116(a3)
   17aee:	0001                	nop
   17af0:	7ae8                	flw	fa0,116(a3)
   17af2:	0001                	nop
   17af4:	7ae8                	flw	fa0,116(a3)
   17af6:	0001                	nop
   17af8:	7af0                	flw	fa2,116(a3)
   17afa:	0001                	nop
   17afc:	7af0                	flw	fa2,116(a3)
   17afe:	0001                	nop
   17b00:	7af8                	flw	fa4,116(a3)
   17b02:	0001                	nop
   17b04:	7af8                	flw	fa4,116(a3)
   17b06:	0001                	nop
   17b08:	7b00                	flw	fs0,48(a4)
   17b0a:	0001                	nop
   17b0c:	7b00                	flw	fs0,48(a4)
   17b0e:	0001                	nop
   17b10:	7b08                	flw	fa0,48(a4)
   17b12:	0001                	nop
   17b14:	7b08                	flw	fa0,48(a4)
   17b16:	0001                	nop
   17b18:	7b10                	flw	fa2,48(a4)
   17b1a:	0001                	nop
   17b1c:	7b10                	flw	fa2,48(a4)
   17b1e:	0001                	nop
   17b20:	7b18                	flw	fa4,48(a4)
   17b22:	0001                	nop
   17b24:	7b18                	flw	fa4,48(a4)
   17b26:	0001                	nop
   17b28:	7b20                	flw	fs0,112(a4)
   17b2a:	0001                	nop
   17b2c:	7b20                	flw	fs0,112(a4)
   17b2e:	0001                	nop
   17b30:	7b28                	flw	fa0,112(a4)
   17b32:	0001                	nop
   17b34:	7b28                	flw	fa0,112(a4)
   17b36:	0001                	nop
   17b38:	7b30                	flw	fa2,112(a4)
   17b3a:	0001                	nop
   17b3c:	7b30                	flw	fa2,112(a4)
   17b3e:	0001                	nop
   17b40:	7b38                	flw	fa4,112(a4)
   17b42:	0001                	nop
   17b44:	7b38                	flw	fa4,112(a4)
   17b46:	0001                	nop
   17b48:	7b40                	flw	fs0,52(a4)
   17b4a:	0001                	nop
   17b4c:	7b40                	flw	fs0,52(a4)
   17b4e:	0001                	nop
   17b50:	7b48                	flw	fa0,52(a4)
   17b52:	0001                	nop
   17b54:	7b48                	flw	fa0,52(a4)
   17b56:	0001                	nop
   17b58:	7b50                	flw	fa2,52(a4)
   17b5a:	0001                	nop
   17b5c:	7b50                	flw	fa2,52(a4)
   17b5e:	0001                	nop
   17b60:	7b58                	flw	fa4,52(a4)
   17b62:	0001                	nop
   17b64:	7b58                	flw	fa4,52(a4)
   17b66:	0001                	nop
   17b68:	7b60                	flw	fs0,116(a4)
   17b6a:	0001                	nop
   17b6c:	7b60                	flw	fs0,116(a4)
   17b6e:	0001                	nop
   17b70:	7b68                	flw	fa0,116(a4)
   17b72:	0001                	nop
   17b74:	7b68                	flw	fa0,116(a4)
   17b76:	0001                	nop
   17b78:	7b70                	flw	fa2,116(a4)
   17b7a:	0001                	nop
   17b7c:	7b70                	flw	fa2,116(a4)
   17b7e:	0001                	nop
   17b80:	7b78                	flw	fa4,116(a4)
   17b82:	0001                	nop
   17b84:	7b78                	flw	fa4,116(a4)
   17b86:	0001                	nop
   17b88:	7b80                	flw	fs0,48(a5)
   17b8a:	0001                	nop
   17b8c:	7b80                	flw	fs0,48(a5)
   17b8e:	0001                	nop
   17b90:	7b88                	flw	fa0,48(a5)
   17b92:	0001                	nop
   17b94:	7b88                	flw	fa0,48(a5)
   17b96:	0001                	nop

Disassembly of section .sdata:

00017b98 <_global_impure_ptr>:
   17b98:	7368                	flw	fa0,100(a4)
   17b9a:	0001                	nop

00017b9c <__dso_handle>:
   17b9c:	0000                	unimp
	...

00017ba0 <_impure_ptr>:
   17ba0:	7368                	flw	fa0,100(a4)
   17ba2:	0001                	nop

00017ba4 <__malloc_sbrk_base>:
   17ba4:	ffff                	0xffff
   17ba6:	ffff                	0xffff

00017ba8 <__malloc_trim_threshold>:
   17ba8:	0000                	unimp
   17baa:	0002                	c.slli64	zero

Disassembly of section .sbss:

00017bac <__malloc_max_total_mem>:
   17bac:	0000                	unimp
	...

00017bb0 <__malloc_max_sbrked_mem>:
   17bb0:	0000                	unimp
	...

00017bb4 <__malloc_top_pad>:
   17bb4:	0000                	unimp
	...

00017bb8 <errno>:
   17bb8:	0000                	unimp
	...

00017bbc <heap_end.0>:
   17bbc:	0000                	unimp
	...

Disassembly of section .bss:

00017bc0 <completed.1>:
   17bc0:	0000                	unimp
	...

00017bc4 <object.0>:
	...

00017bdc <__malloc_current_mallinfo>:
	...

Disassembly of section .comment:

00000000 <.comment>:
   0:	3a434347          	fmsub.d	ft6,ft6,ft4,ft7,rmm
   4:	2820                	fld	fs0,80(s0)
   6:	29554e47          	fmsub.s	ft8,fa0,fs5,ft5,rmm
   a:	3120                	fld	fs0,96(a0)
   c:	2e31                	jal	328 <main-0xfd4c>
   e:	2e31                	jal	32a <main-0xfd4a>
  10:	0030                	addi	a2,sp,8

Disassembly of section .riscv.attributes:

00000000 <.riscv.attributes>:
   0:	2041                	jal	80 <main-0xfff4>
   2:	0000                	unimp
   4:	7200                	flw	fs0,32(a2)
   6:	7369                	lui	t1,0xffffa
   8:	01007663          	bgeu	zero,a6,14 <main-0x10060>
   c:	0016                	c.slli	zero,0x5
   e:	0000                	unimp
  10:	1004                	addi	s1,sp,32
  12:	7205                	lui	tp,0xfffe1
  14:	3376                	fld	ft6,376(sp)
  16:	6932                	flw	fs2,12(sp)
  18:	7032                	flw	ft0,44(sp)
  1a:	5f30                	lw	a2,120(a4)
  1c:	326d                	jal	fffff9c6 <__BSS_END__+0xfffe7dc2>
  1e:	3070                	fld	fa2,224(s0)
	...
