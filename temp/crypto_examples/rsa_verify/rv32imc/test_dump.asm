
test_rsa.elf:     file format elf32-littleriscv


Disassembly of section .text:

00010074 <main>:
   10074:	81010113          	addi	sp,sp,-2032
   10078:	7e812423          	sw	s0,2024(sp)
   1007c:	fffff5b7          	lui	a1,0xfffff
   10080:	000017b7          	lui	a5,0x1
   10084:	0b01a503          	lw	a0,176(gp) # 12bf8 <d0inv>
   10088:	70058593          	addi	a1,a1,1792 # fffff700 <__BSS_END__+0xfffecae4>
   1008c:	90078793          	addi	a5,a5,-1792 # 900 <main-0xf774>
   10090:	7e112623          	sw	ra,2028(sp)
   10094:	00b787b3          	add	a5,a5,a1
   10098:	ee010113          	addi	sp,sp,-288
   1009c:	002785b3          	add	a1,a5,sp
   100a0:	30010613          	addi	a2,sp,768
   100a4:	39c000ef          	jal	ra,10440 <mod_pow.constprop.0>
   100a8:	0b01a583          	lw	a1,176(gp) # 12bf8 <d0inv>
   100ac:	00012637          	lui	a2,0x12
   100b0:	34860693          	addi	a3,a2,840 # 12348 <n>
   100b4:	18068513          	addi	a0,a3,384
   100b8:	60010793          	addi	a5,sp,1536
   100bc:	18010713          	addi	a4,sp,384
   100c0:	30068693          	addi	a3,a3,768
   100c4:	34860613          	addi	a2,a2,840
   100c8:	464000ef          	jal	ra,1052c <asm_mod_pow>
   100cc:	12010113          	addi	sp,sp,288
   100d0:	7ec12083          	lw	ra,2028(sp)
   100d4:	7e812403          	lw	s0,2024(sp)
   100d8:	00000513          	li	a0,0
   100dc:	7f010113          	addi	sp,sp,2032
   100e0:	00008067          	ret

000100e4 <register_fini>:
   100e4:	00000793          	li	a5,0
   100e8:	00078863          	beqz	a5,100f8 <register_fini+0x14>
   100ec:	00001517          	auipc	a0,0x1
   100f0:	11c50513          	addi	a0,a0,284 # 11208 <__libc_fini_array>
   100f4:	1000106f          	j	111f4 <atexit>
   100f8:	00008067          	ret

000100fc <_start>:
   100fc:	00003197          	auipc	gp,0x3
   10100:	a4c18193          	addi	gp,gp,-1460 # 12b48 <__global_pointer$>
   10104:	0b818513          	addi	a0,gp,184 # 12c00 <completed.1>
   10108:	0d418613          	addi	a2,gp,212 # 12c1c <__BSS_END__>
   1010c:	40a60633          	sub	a2,a2,a0
   10110:	00000593          	li	a1,0
   10114:	6e5000ef          	jal	ra,10ff8 <memset>
   10118:	00001517          	auipc	a0,0x1
   1011c:	0dc50513          	addi	a0,a0,220 # 111f4 <atexit>
   10120:	00050863          	beqz	a0,10130 <_start+0x34>
   10124:	00001517          	auipc	a0,0x1
   10128:	0e450513          	addi	a0,a0,228 # 11208 <__libc_fini_array>
   1012c:	0c8010ef          	jal	ra,111f4 <atexit>
   10130:	635000ef          	jal	ra,10f64 <__libc_init_array>
   10134:	00012503          	lw	a0,0(sp)
   10138:	00410593          	addi	a1,sp,4
   1013c:	00000613          	li	a2,0
   10140:	f35ff0ef          	jal	ra,10074 <main>
   10144:	5f10006f          	j	10f34 <exit>

00010148 <__do_global_dtors_aux>:
   10148:	ff010113          	addi	sp,sp,-16
   1014c:	00812423          	sw	s0,8(sp)
   10150:	0b818413          	addi	s0,gp,184 # 12c00 <completed.1>
   10154:	00044783          	lbu	a5,0(s0)
   10158:	00112623          	sw	ra,12(sp)
   1015c:	02079263          	bnez	a5,10180 <__do_global_dtors_aux+0x38>
   10160:	00000793          	li	a5,0
   10164:	00078a63          	beqz	a5,10178 <__do_global_dtors_aux+0x30>
   10168:	00002517          	auipc	a0,0x2
   1016c:	1cc50513          	addi	a0,a0,460 # 12334 <__FRAME_END__>
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
   10198:	0bc18593          	addi	a1,gp,188 # 12c04 <object.0>
   1019c:	00002517          	auipc	a0,0x2
   101a0:	19850513          	addi	a0,a0,408 # 12334 <__FRAME_END__>
   101a4:	00000317          	auipc	t1,0x0
   101a8:	00000067          	jr	zero # 0 <main-0x10074>
   101ac:	00008067          	ret

000101b0 <ge_mod.constprop.0>:
   101b0:	000125b7          	lui	a1,0x12
   101b4:	34858793          	addi	a5,a1,840 # 12348 <n>
   101b8:	17c50513          	addi	a0,a0,380
   101bc:	17c78793          	addi	a5,a5,380
   101c0:	34858593          	addi	a1,a1,840
   101c4:	0100006f          	j	101d4 <ge_mod.constprop.0+0x24>
   101c8:	02d76463          	bltu	a4,a3,101f0 <ge_mod.constprop.0+0x40>
   101cc:	02b78263          	beq	a5,a1,101f0 <ge_mod.constprop.0+0x40>
   101d0:	00060793          	mv	a5,a2
   101d4:	00052683          	lw	a3,0(a0)
   101d8:	0007a703          	lw	a4,0(a5)
   101dc:	ffc78613          	addi	a2,a5,-4
   101e0:	ffc50513          	addi	a0,a0,-4
   101e4:	fee6f2e3          	bgeu	a3,a4,101c8 <ge_mod.constprop.0+0x18>
   101e8:	00000513          	li	a0,0
   101ec:	00008067          	ret
   101f0:	00100513          	li	a0,1
   101f4:	00008067          	ret

000101f8 <sub_mod.constprop.0>:
   101f8:	00012637          	lui	a2,0x12
   101fc:	34860613          	addi	a2,a2,840 # 12348 <n>
   10200:	18060813          	addi	a6,a2,384
   10204:	00000793          	li	a5,0
   10208:	00000593          	li	a1,0
   1020c:	00052703          	lw	a4,0(a0)
   10210:	00062683          	lw	a3,0(a2)
   10214:	00460613          	addi	a2,a2,4
   10218:	00f707b3          	add	a5,a4,a5
   1021c:	40d786b3          	sub	a3,a5,a3
   10220:	00e7b733          	sltu	a4,a5,a4
   10224:	00b70733          	add	a4,a4,a1
   10228:	00d7b7b3          	sltu	a5,a5,a3
   1022c:	00d52023          	sw	a3,0(a0)
   10230:	40f707b3          	sub	a5,a4,a5
   10234:	41f7d593          	srai	a1,a5,0x1f
   10238:	00450513          	addi	a0,a0,4
   1023c:	fcc818e3          	bne	a6,a2,1020c <sub_mod.constprop.0+0x14>
   10240:	00008067          	ret

00010244 <mul32>:
   10244:	00058793          	mv	a5,a1
   10248:	02b535b3          	mulhu	a1,a0,a1
   1024c:	02f50533          	mul	a0,a0,a5
   10250:	00008067          	ret

00010254 <mula32>:
   10254:	02b507b3          	mul	a5,a0,a1
   10258:	02b535b3          	mulhu	a1,a0,a1
   1025c:	00c78533          	add	a0,a5,a2
   10260:	00f537b3          	sltu	a5,a0,a5
   10264:	00b785b3          	add	a1,a5,a1
   10268:	00008067          	ret

0001026c <mulaa32>:
   1026c:	02b50733          	mul	a4,a0,a1
   10270:	00d606b3          	add	a3,a2,a3
   10274:	00c6b633          	sltu	a2,a3,a2
   10278:	02b537b3          	mulhu	a5,a0,a1
   1027c:	00d70533          	add	a0,a4,a3
   10280:	00e535b3          	sltu	a1,a0,a4
   10284:	00c787b3          	add	a5,a5,a2
   10288:	00f585b3          	add	a1,a1,a5
   1028c:	00008067          	ret

00010290 <mont_mul_add.constprop.0>:
   10290:	fd010113          	addi	sp,sp,-48
   10294:	01612823          	sw	s6,16(sp)
   10298:	00058b13          	mv	s6,a1
   1029c:	01712623          	sw	s7,12(sp)
   102a0:	0006a583          	lw	a1,0(a3)
   102a4:	00060b93          	mv	s7,a2
   102a8:	000b2603          	lw	a2,0(s6)
   102ac:	01512a23          	sw	s5,20(sp)
   102b0:	00050a93          	mv	s5,a0
   102b4:	000b8513          	mv	a0,s7
   102b8:	02112623          	sw	ra,44(sp)
   102bc:	02812423          	sw	s0,40(sp)
   102c0:	02912223          	sw	s1,36(sp)
   102c4:	03212023          	sw	s2,32(sp)
   102c8:	01312e23          	sw	s3,28(sp)
   102cc:	01412c23          	sw	s4,24(sp)
   102d0:	01812423          	sw	s8,8(sp)
   102d4:	00068a13          	mv	s4,a3
   102d8:	f7dff0ef          	jal	ra,10254 <mula32>
   102dc:	03550ab3          	mul	s5,a0,s5
   102e0:	00012c37          	lui	s8,0x12
   102e4:	348c0c13          	addi	s8,s8,840 # 12348 <n>
   102e8:	00058413          	mv	s0,a1
   102ec:	000c2583          	lw	a1,0(s8)
   102f0:	00050613          	mv	a2,a0
   102f4:	004c0913          	addi	s2,s8,4
   102f8:	004a0a13          	addi	s4,s4,4
   102fc:	000b0993          	mv	s3,s6
   10300:	180c0c13          	addi	s8,s8,384
   10304:	000a8513          	mv	a0,s5
   10308:	f4dff0ef          	jal	ra,10254 <mula32>
   1030c:	00058493          	mv	s1,a1
   10310:	0049a603          	lw	a2,4(s3)
   10314:	000a2583          	lw	a1,0(s4)
   10318:	00040693          	mv	a3,s0
   1031c:	000b8513          	mv	a0,s7
   10320:	f4dff0ef          	jal	ra,1026c <mulaa32>
   10324:	00058413          	mv	s0,a1
   10328:	00092583          	lw	a1,0(s2)
   1032c:	00050613          	mv	a2,a0
   10330:	00048693          	mv	a3,s1
   10334:	000a8513          	mv	a0,s5
   10338:	f35ff0ef          	jal	ra,1026c <mulaa32>
   1033c:	00a9a023          	sw	a0,0(s3)
   10340:	00490913          	addi	s2,s2,4
   10344:	00058493          	mv	s1,a1
   10348:	004a0a13          	addi	s4,s4,4
   1034c:	00498993          	addi	s3,s3,4
   10350:	fd2c10e3          	bne	s8,s2,10310 <mont_mul_add.constprop.0+0x80>
   10354:	00858433          	add	s0,a1,s0
   10358:	168b2e23          	sw	s0,380(s6)
   1035c:	02b46a63          	bltu	s0,a1,10390 <mont_mul_add.constprop.0+0x100>
   10360:	02c12083          	lw	ra,44(sp)
   10364:	02812403          	lw	s0,40(sp)
   10368:	02412483          	lw	s1,36(sp)
   1036c:	02012903          	lw	s2,32(sp)
   10370:	01c12983          	lw	s3,28(sp)
   10374:	01812a03          	lw	s4,24(sp)
   10378:	01412a83          	lw	s5,20(sp)
   1037c:	01012b03          	lw	s6,16(sp)
   10380:	00c12b83          	lw	s7,12(sp)
   10384:	00812c03          	lw	s8,8(sp)
   10388:	03010113          	addi	sp,sp,48
   1038c:	00008067          	ret
   10390:	02812403          	lw	s0,40(sp)
   10394:	02c12083          	lw	ra,44(sp)
   10398:	02412483          	lw	s1,36(sp)
   1039c:	02012903          	lw	s2,32(sp)
   103a0:	01c12983          	lw	s3,28(sp)
   103a4:	01812a03          	lw	s4,24(sp)
   103a8:	01412a83          	lw	s5,20(sp)
   103ac:	00c12b83          	lw	s7,12(sp)
   103b0:	00812c03          	lw	s8,8(sp)
   103b4:	000b0513          	mv	a0,s6
   103b8:	01012b03          	lw	s6,16(sp)
   103bc:	03010113          	addi	sp,sp,48
   103c0:	e39ff06f          	j	101f8 <sub_mod.constprop.0>

000103c4 <mont_mul.constprop.0>:
   103c4:	fe010113          	addi	sp,sp,-32
   103c8:	00912a23          	sw	s1,20(sp)
   103cc:	00058493          	mv	s1,a1
   103d0:	00812c23          	sw	s0,24(sp)
   103d4:	01312623          	sw	s3,12(sp)
   103d8:	00060413          	mv	s0,a2
   103dc:	00050993          	mv	s3,a0
   103e0:	18000613          	li	a2,384
   103e4:	00000593          	li	a1,0
   103e8:	00048513          	mv	a0,s1
   103ec:	01212823          	sw	s2,16(sp)
   103f0:	01412423          	sw	s4,8(sp)
   103f4:	00112e23          	sw	ra,28(sp)
   103f8:	00068913          	mv	s2,a3
   103fc:	18040a13          	addi	s4,s0,384
   10400:	3f9000ef          	jal	ra,10ff8 <memset>
   10404:	00042603          	lw	a2,0(s0)
   10408:	00090693          	mv	a3,s2
   1040c:	00440413          	addi	s0,s0,4
   10410:	00048593          	mv	a1,s1
   10414:	00098513          	mv	a0,s3
   10418:	e79ff0ef          	jal	ra,10290 <mont_mul_add.constprop.0>
   1041c:	fe8a14e3          	bne	s4,s0,10404 <mont_mul.constprop.0+0x40>
   10420:	01c12083          	lw	ra,28(sp)
   10424:	01812403          	lw	s0,24(sp)
   10428:	01412483          	lw	s1,20(sp)
   1042c:	01012903          	lw	s2,16(sp)
   10430:	00c12983          	lw	s3,12(sp)
   10434:	00812a03          	lw	s4,8(sp)
   10438:	02010113          	addi	sp,sp,32
   1043c:	00008067          	ret

00010440 <mod_pow.constprop.0>:
   10440:	000126b7          	lui	a3,0x12
   10444:	fe010113          	addi	sp,sp,-32
   10448:	34868693          	addi	a3,a3,840 # 12348 <n>
   1044c:	00812c23          	sw	s0,24(sp)
   10450:	01512223          	sw	s5,4(sp)
   10454:	00060413          	mv	s0,a2
   10458:	30068a93          	addi	s5,a3,768
   1045c:	01412423          	sw	s4,8(sp)
   10460:	18068693          	addi	a3,a3,384
   10464:	00058a13          	mv	s4,a1
   10468:	000a8613          	mv	a2,s5
   1046c:	00040593          	mv	a1,s0
   10470:	00912a23          	sw	s1,20(sp)
   10474:	01212823          	sw	s2,16(sp)
   10478:	01312623          	sw	s3,12(sp)
   1047c:	00112e23          	sw	ra,28(sp)
   10480:	00050993          	mv	s3,a0
   10484:	18040913          	addi	s2,s0,384
   10488:	f3dff0ef          	jal	ra,103c4 <mont_mul.constprop.0>
   1048c:	00800493          	li	s1,8
   10490:	00040693          	mv	a3,s0
   10494:	00040613          	mv	a2,s0
   10498:	00090593          	mv	a1,s2
   1049c:	00098513          	mv	a0,s3
   104a0:	f25ff0ef          	jal	ra,103c4 <mont_mul.constprop.0>
   104a4:	fff48493          	addi	s1,s1,-1
   104a8:	00090693          	mv	a3,s2
   104ac:	00090613          	mv	a2,s2
   104b0:	00040593          	mv	a1,s0
   104b4:	00098513          	mv	a0,s3
   104b8:	f0dff0ef          	jal	ra,103c4 <mont_mul.constprop.0>
   104bc:	fc049ae3          	bnez	s1,10490 <mod_pow.constprop.0+0x50>
   104c0:	00098513          	mv	a0,s3
   104c4:	000a8693          	mv	a3,s5
   104c8:	00040613          	mv	a2,s0
   104cc:	000a0593          	mv	a1,s4
   104d0:	ef5ff0ef          	jal	ra,103c4 <mont_mul.constprop.0>
   104d4:	000a0513          	mv	a0,s4
   104d8:	cd9ff0ef          	jal	ra,101b0 <ge_mod.constprop.0>
   104dc:	02051463          	bnez	a0,10504 <mod_pow.constprop.0+0xc4>
   104e0:	01c12083          	lw	ra,28(sp)
   104e4:	01812403          	lw	s0,24(sp)
   104e8:	01412483          	lw	s1,20(sp)
   104ec:	01012903          	lw	s2,16(sp)
   104f0:	00c12983          	lw	s3,12(sp)
   104f4:	00812a03          	lw	s4,8(sp)
   104f8:	00412a83          	lw	s5,4(sp)
   104fc:	02010113          	addi	sp,sp,32
   10500:	00008067          	ret
   10504:	01812403          	lw	s0,24(sp)
   10508:	01c12083          	lw	ra,28(sp)
   1050c:	01412483          	lw	s1,20(sp)
   10510:	01012903          	lw	s2,16(sp)
   10514:	00c12983          	lw	s3,12(sp)
   10518:	00412a83          	lw	s5,4(sp)
   1051c:	000a0513          	mv	a0,s4
   10520:	00812a03          	lw	s4,8(sp)
   10524:	02010113          	addi	sp,sp,32
   10528:	cd1ff06f          	j	101f8 <sub_mod.constprop.0>

0001052c <asm_mod_pow>:
   1052c:	fe010113          	addi	sp,sp,-32
   10530:	00112e23          	sw	ra,28(sp)
   10534:	00812c23          	sw	s0,24(sp)
   10538:	01b12a23          	sw	s11,20(sp)
   1053c:	01212823          	sw	s2,16(sp)
   10540:	01312623          	sw	s3,12(sp)
   10544:	01412423          	sw	s4,8(sp)
   10548:	01512223          	sw	s5,4(sp)
   1054c:	00060413          	mv	s0,a2
   10550:	00011637          	lui	a2,0x11
   10554:	61860613          	addi	a2,a2,1560 # 11618 <__errno+0x2ec>
   10558:	30060a93          	addi	s5,a2,768
   1055c:	18060613          	addi	a2,a2,384
   10560:	00058a13          	mv	s4,a1
   10564:	000a8693          	mv	a3,s5
   10568:	00040593          	mv	a1,s0
   1056c:	00050993          	mv	s3,a0
   10570:	18040913          	addi	s2,s0,384
   10574:	fe010113          	addi	sp,sp,-32
   10578:	00112e23          	sw	ra,28(sp)
   1057c:	00812c23          	sw	s0,24(sp)
   10580:	01b12a23          	sw	s11,20(sp)
   10584:	01212823          	sw	s2,16(sp)
   10588:	01312623          	sw	s3,12(sp)
   1058c:	01412423          	sw	s4,8(sp)
   10590:	00050413          	mv	s0,a0
   10594:	00058d93          	mv	s11,a1
   10598:	00060913          	mv	s2,a2
   1059c:	00068993          	mv	s3,a3
   105a0:	180d8a13          	addi	s4,s11,384

000105a4 <w_start0>:
   105a4:	014dd863          	bge	s11,s4,105b4 <w_end0>
   105a8:	000da023          	sw	zero,0(s11)
   105ac:	004d8d93          	addi	s11,s11,4
   105b0:	ff5ff06f          	j	105a4 <w_start0>

000105b4 <w_end0>:
   105b4:	00058d93          	mv	s11,a1
   105b8:	18090a13          	addi	s4,s2,384

000105bc <w_start1>:
   105bc:	1d495463          	bge	s2,s4,10784 <w_end1>
   105c0:	000d8593          	mv	a1,s11
   105c4:	00040513          	mv	a0,s0
   105c8:	00098693          	mv	a3,s3
   105cc:	00092603          	lw	a2,0(s2)
   105d0:	fd010113          	addi	sp,sp,-48
   105d4:	02112623          	sw	ra,44(sp)
   105d8:	02812423          	sw	s0,40(sp)
   105dc:	03b12223          	sw	s11,36(sp)
   105e0:	03212023          	sw	s2,32(sp)
   105e4:	01312e23          	sw	s3,28(sp)
   105e8:	01412c23          	sw	s4,24(sp)
   105ec:	01612823          	sw	s6,16(sp)
   105f0:	01512a23          	sw	s5,20(sp)
   105f4:	01712623          	sw	s7,12(sp)
   105f8:	01812423          	sw	s8,8(sp)
   105fc:	00058b13          	mv	s6,a1
   10600:	0006a583          	lw	a1,0(a3)
   10604:	00060b93          	mv	s7,a2
   10608:	000b2603          	lw	a2,0(s6)
   1060c:	00050a93          	mv	s5,a0
   10610:	000b8513          	mv	a0,s7
   10614:	00068a13          	mv	s4,a3
   10618:	02b507b3          	mul	a5,a0,a1
   1061c:	02b535b3          	mulhu	a1,a0,a1
   10620:	00c78533          	add	a0,a5,a2
   10624:	00f537b3          	sltu	a5,a0,a5
   10628:	00f585b3          	add	a1,a1,a5
   1062c:	03550ab3          	mul	s5,a0,s5
   10630:	00011c37          	lui	s8,0x11
   10634:	618c0c13          	addi	s8,s8,1560 # 11618 <__errno+0x2ec>
   10638:	00058413          	mv	s0,a1
   1063c:	000c2583          	lw	a1,0(s8)
   10640:	00050613          	mv	a2,a0
   10644:	004c0913          	addi	s2,s8,4
   10648:	004a0a13          	addi	s4,s4,4
   1064c:	000b0993          	mv	s3,s6
   10650:	180c0c13          	addi	s8,s8,384
   10654:	000a8513          	mv	a0,s5
   10658:	02b507b3          	mul	a5,a0,a1
   1065c:	02b535b3          	mulhu	a1,a0,a1
   10660:	00c78533          	add	a0,a5,a2
   10664:	00f537b3          	sltu	a5,a0,a5
   10668:	00f585b3          	add	a1,a1,a5
   1066c:	00058d93          	mv	s11,a1

00010670 <w_start2>:
   10670:	09895063          	bge	s2,s8,106f0 <w_end2>
   10674:	0049a603          	lw	a2,4(s3)
   10678:	000a2583          	lw	a1,0(s4)
   1067c:	00040693          	mv	a3,s0
   10680:	000b8513          	mv	a0,s7
   10684:	02b507b3          	mul	a5,a0,a1
   10688:	02b535b3          	mulhu	a1,a0,a1
   1068c:	00c78533          	add	a0,a5,a2
   10690:	00f537b3          	sltu	a5,a0,a5
   10694:	00f585b3          	add	a1,a1,a5
   10698:	00d50533          	add	a0,a0,a3
   1069c:	00d537b3          	sltu	a5,a0,a3
   106a0:	00f585b3          	add	a1,a1,a5
   106a4:	00058413          	mv	s0,a1
   106a8:	00092583          	lw	a1,0(s2)
   106ac:	00050613          	mv	a2,a0
   106b0:	000d8693          	mv	a3,s11
   106b4:	000a8513          	mv	a0,s5
   106b8:	02b507b3          	mul	a5,a0,a1
   106bc:	02b535b3          	mulhu	a1,a0,a1
   106c0:	00c78533          	add	a0,a5,a2
   106c4:	00f537b3          	sltu	a5,a0,a5
   106c8:	00f585b3          	add	a1,a1,a5
   106cc:	00d50533          	add	a0,a0,a3
   106d0:	00d537b3          	sltu	a5,a0,a3
   106d4:	00f585b3          	add	a1,a1,a5
   106d8:	00a9a023          	sw	a0,0(s3)
   106dc:	00490913          	addi	s2,s2,4
   106e0:	00058d93          	mv	s11,a1
   106e4:	004a0a13          	addi	s4,s4,4
   106e8:	00498993          	addi	s3,s3,4
   106ec:	f85ff06f          	j	10670 <w_start2>

000106f0 <w_end2>:
   106f0:	01b40433          	add	s0,s0,s11
   106f4:	0089a023          	sw	s0,0(s3)
   106f8:	01b44463          	blt	s0,s11,10700 <if_true3>
   106fc:	0540006f          	j	10750 <if_end3>

00010700 <if_true3>:
   10700:	000b0513          	mv	a0,s6
   10704:	00011637          	lui	a2,0x11
   10708:	61860613          	addi	a2,a2,1560 # 11618 <__errno+0x2ec>
   1070c:	18060813          	addi	a6,a2,384
   10710:	00000793          	li	a5,0
   10714:	00000593          	li	a1,0

00010718 <w_start4>:
   10718:	03060c63          	beq	a2,a6,10750 <if_end3>
   1071c:	00052703          	lw	a4,0(a0)
   10720:	00062683          	lw	a3,0(a2)
   10724:	00460613          	addi	a2,a2,4
   10728:	00e787b3          	add	a5,a5,a4
   1072c:	40d786b3          	sub	a3,a5,a3
   10730:	00e7b733          	sltu	a4,a5,a4
   10734:	00b70733          	add	a4,a4,a1
   10738:	00d7b7b3          	sltu	a5,a5,a3
   1073c:	00d52023          	sw	a3,0(a0)
   10740:	00450513          	addi	a0,a0,4
   10744:	40f707b3          	sub	a5,a4,a5
   10748:	41f7d593          	srai	a1,a5,0x1f
   1074c:	fcdff06f          	j	10718 <w_start4>

00010750 <if_end3>:
   10750:	02c12083          	lw	ra,44(sp)
   10754:	02812403          	lw	s0,40(sp)
   10758:	02412d83          	lw	s11,36(sp)
   1075c:	02012903          	lw	s2,32(sp)
   10760:	01c12983          	lw	s3,28(sp)
   10764:	01812a03          	lw	s4,24(sp)
   10768:	01412a83          	lw	s5,20(sp)
   1076c:	01012b03          	lw	s6,16(sp)
   10770:	00c12b83          	lw	s7,12(sp)
   10774:	00812c03          	lw	s8,8(sp)
   10778:	03010113          	addi	sp,sp,48
   1077c:	00490913          	addi	s2,s2,4
   10780:	e3dff06f          	j	105bc <w_start1>

00010784 <w_end1>:
   10784:	01c12083          	lw	ra,28(sp)
   10788:	01812403          	lw	s0,24(sp)
   1078c:	01412d83          	lw	s11,20(sp)
   10790:	01012903          	lw	s2,16(sp)
   10794:	00c12983          	lw	s3,12(sp)
   10798:	00812a03          	lw	s4,8(sp)
   1079c:	02010113          	addi	sp,sp,32
   107a0:	00800d93          	li	s11,8

000107a4 <w_start5>:
   107a4:	49b05263          	blez	s11,10c28 <w_end5>
   107a8:	00040693          	mv	a3,s0
   107ac:	00040613          	mv	a2,s0
   107b0:	00090593          	mv	a1,s2
   107b4:	00098513          	mv	a0,s3
   107b8:	fe010113          	addi	sp,sp,-32
   107bc:	00112e23          	sw	ra,28(sp)
   107c0:	00812c23          	sw	s0,24(sp)
   107c4:	01b12a23          	sw	s11,20(sp)
   107c8:	01212823          	sw	s2,16(sp)
   107cc:	01312623          	sw	s3,12(sp)
   107d0:	01412423          	sw	s4,8(sp)
   107d4:	00050413          	mv	s0,a0
   107d8:	00058d93          	mv	s11,a1
   107dc:	00060913          	mv	s2,a2
   107e0:	00068993          	mv	s3,a3
   107e4:	180d8a13          	addi	s4,s11,384

000107e8 <w_start6>:
   107e8:	014dd863          	bge	s11,s4,107f8 <w_end6>
   107ec:	000da023          	sw	zero,0(s11)
   107f0:	004d8d93          	addi	s11,s11,4
   107f4:	ff5ff06f          	j	107e8 <w_start6>

000107f8 <w_end6>:
   107f8:	00058d93          	mv	s11,a1
   107fc:	18090a13          	addi	s4,s2,384

00010800 <w_start7>:
   10800:	1d495463          	bge	s2,s4,109c8 <w_end7>
   10804:	000d8593          	mv	a1,s11
   10808:	00040513          	mv	a0,s0
   1080c:	00098693          	mv	a3,s3
   10810:	00092603          	lw	a2,0(s2)
   10814:	fd010113          	addi	sp,sp,-48
   10818:	02112623          	sw	ra,44(sp)
   1081c:	02812423          	sw	s0,40(sp)
   10820:	03b12223          	sw	s11,36(sp)
   10824:	03212023          	sw	s2,32(sp)
   10828:	01312e23          	sw	s3,28(sp)
   1082c:	01412c23          	sw	s4,24(sp)
   10830:	01612823          	sw	s6,16(sp)
   10834:	01512a23          	sw	s5,20(sp)
   10838:	01712623          	sw	s7,12(sp)
   1083c:	01812423          	sw	s8,8(sp)
   10840:	00058b13          	mv	s6,a1
   10844:	0006a583          	lw	a1,0(a3)
   10848:	00060b93          	mv	s7,a2
   1084c:	000b2603          	lw	a2,0(s6)
   10850:	00050a93          	mv	s5,a0
   10854:	000b8513          	mv	a0,s7
   10858:	00068a13          	mv	s4,a3
   1085c:	02b507b3          	mul	a5,a0,a1
   10860:	02b535b3          	mulhu	a1,a0,a1
   10864:	00c78533          	add	a0,a5,a2
   10868:	00f537b3          	sltu	a5,a0,a5
   1086c:	00f585b3          	add	a1,a1,a5
   10870:	03550ab3          	mul	s5,a0,s5
   10874:	00011c37          	lui	s8,0x11
   10878:	618c0c13          	addi	s8,s8,1560 # 11618 <__errno+0x2ec>
   1087c:	00058413          	mv	s0,a1
   10880:	000c2583          	lw	a1,0(s8)
   10884:	00050613          	mv	a2,a0
   10888:	004c0913          	addi	s2,s8,4
   1088c:	004a0a13          	addi	s4,s4,4
   10890:	000b0993          	mv	s3,s6
   10894:	180c0c13          	addi	s8,s8,384
   10898:	000a8513          	mv	a0,s5
   1089c:	02b507b3          	mul	a5,a0,a1
   108a0:	02b535b3          	mulhu	a1,a0,a1
   108a4:	00c78533          	add	a0,a5,a2
   108a8:	00f537b3          	sltu	a5,a0,a5
   108ac:	00f585b3          	add	a1,a1,a5
   108b0:	00058d93          	mv	s11,a1

000108b4 <w_start8>:
   108b4:	09895063          	bge	s2,s8,10934 <w_end8>
   108b8:	0049a603          	lw	a2,4(s3)
   108bc:	000a2583          	lw	a1,0(s4)
   108c0:	00040693          	mv	a3,s0
   108c4:	000b8513          	mv	a0,s7
   108c8:	02b507b3          	mul	a5,a0,a1
   108cc:	02b535b3          	mulhu	a1,a0,a1
   108d0:	00c78533          	add	a0,a5,a2
   108d4:	00f537b3          	sltu	a5,a0,a5
   108d8:	00f585b3          	add	a1,a1,a5
   108dc:	00d50533          	add	a0,a0,a3
   108e0:	00d537b3          	sltu	a5,a0,a3
   108e4:	00f585b3          	add	a1,a1,a5
   108e8:	00058413          	mv	s0,a1
   108ec:	00092583          	lw	a1,0(s2)
   108f0:	00050613          	mv	a2,a0
   108f4:	000d8693          	mv	a3,s11
   108f8:	000a8513          	mv	a0,s5
   108fc:	02b507b3          	mul	a5,a0,a1
   10900:	02b535b3          	mulhu	a1,a0,a1
   10904:	00c78533          	add	a0,a5,a2
   10908:	00f537b3          	sltu	a5,a0,a5
   1090c:	00f585b3          	add	a1,a1,a5
   10910:	00d50533          	add	a0,a0,a3
   10914:	00d537b3          	sltu	a5,a0,a3
   10918:	00f585b3          	add	a1,a1,a5
   1091c:	00a9a023          	sw	a0,0(s3)
   10920:	00490913          	addi	s2,s2,4
   10924:	00058d93          	mv	s11,a1
   10928:	004a0a13          	addi	s4,s4,4
   1092c:	00498993          	addi	s3,s3,4
   10930:	f85ff06f          	j	108b4 <w_start8>

00010934 <w_end8>:
   10934:	01b40433          	add	s0,s0,s11
   10938:	0089a023          	sw	s0,0(s3)
   1093c:	01b44463          	blt	s0,s11,10944 <if_true9>
   10940:	0540006f          	j	10994 <if_end9>

00010944 <if_true9>:
   10944:	000b0513          	mv	a0,s6
   10948:	00011637          	lui	a2,0x11
   1094c:	61860613          	addi	a2,a2,1560 # 11618 <__errno+0x2ec>
   10950:	18060813          	addi	a6,a2,384
   10954:	00000793          	li	a5,0
   10958:	00000593          	li	a1,0

0001095c <w_start10>:
   1095c:	03060c63          	beq	a2,a6,10994 <if_end9>
   10960:	00052703          	lw	a4,0(a0)
   10964:	00062683          	lw	a3,0(a2)
   10968:	00460613          	addi	a2,a2,4
   1096c:	00e787b3          	add	a5,a5,a4
   10970:	40d786b3          	sub	a3,a5,a3
   10974:	00e7b733          	sltu	a4,a5,a4
   10978:	00b70733          	add	a4,a4,a1
   1097c:	00d7b7b3          	sltu	a5,a5,a3
   10980:	00d52023          	sw	a3,0(a0)
   10984:	00450513          	addi	a0,a0,4
   10988:	40f707b3          	sub	a5,a4,a5
   1098c:	41f7d593          	srai	a1,a5,0x1f
   10990:	fcdff06f          	j	1095c <w_start10>

00010994 <if_end9>:
   10994:	02c12083          	lw	ra,44(sp)
   10998:	02812403          	lw	s0,40(sp)
   1099c:	02412d83          	lw	s11,36(sp)
   109a0:	02012903          	lw	s2,32(sp)
   109a4:	01c12983          	lw	s3,28(sp)
   109a8:	01812a03          	lw	s4,24(sp)
   109ac:	01412a83          	lw	s5,20(sp)
   109b0:	01012b03          	lw	s6,16(sp)
   109b4:	00c12b83          	lw	s7,12(sp)
   109b8:	00812c03          	lw	s8,8(sp)
   109bc:	03010113          	addi	sp,sp,48
   109c0:	00490913          	addi	s2,s2,4
   109c4:	e3dff06f          	j	10800 <w_start7>

000109c8 <w_end7>:
   109c8:	01c12083          	lw	ra,28(sp)
   109cc:	01812403          	lw	s0,24(sp)
   109d0:	01412d83          	lw	s11,20(sp)
   109d4:	01012903          	lw	s2,16(sp)
   109d8:	00c12983          	lw	s3,12(sp)
   109dc:	00812a03          	lw	s4,8(sp)
   109e0:	02010113          	addi	sp,sp,32
   109e4:	00090693          	mv	a3,s2
   109e8:	00090613          	mv	a2,s2
   109ec:	00040593          	mv	a1,s0
   109f0:	00098513          	mv	a0,s3
   109f4:	fe010113          	addi	sp,sp,-32
   109f8:	00112e23          	sw	ra,28(sp)
   109fc:	00812c23          	sw	s0,24(sp)
   10a00:	01b12a23          	sw	s11,20(sp)
   10a04:	01212823          	sw	s2,16(sp)
   10a08:	01312623          	sw	s3,12(sp)
   10a0c:	01412423          	sw	s4,8(sp)
   10a10:	00050413          	mv	s0,a0
   10a14:	00058d93          	mv	s11,a1
   10a18:	00060913          	mv	s2,a2
   10a1c:	00068993          	mv	s3,a3
   10a20:	180d8a13          	addi	s4,s11,384

00010a24 <w_start11>:
   10a24:	014dd863          	bge	s11,s4,10a34 <w_end11>
   10a28:	000da023          	sw	zero,0(s11)
   10a2c:	004d8d93          	addi	s11,s11,4
   10a30:	ff5ff06f          	j	10a24 <w_start11>

00010a34 <w_end11>:
   10a34:	00058d93          	mv	s11,a1
   10a38:	18090a13          	addi	s4,s2,384

00010a3c <w_start12>:
   10a3c:	1d495463          	bge	s2,s4,10c04 <w_end12>
   10a40:	000d8593          	mv	a1,s11
   10a44:	00040513          	mv	a0,s0
   10a48:	00098693          	mv	a3,s3
   10a4c:	00092603          	lw	a2,0(s2)
   10a50:	fd010113          	addi	sp,sp,-48
   10a54:	02112623          	sw	ra,44(sp)
   10a58:	02812423          	sw	s0,40(sp)
   10a5c:	03b12223          	sw	s11,36(sp)
   10a60:	03212023          	sw	s2,32(sp)
   10a64:	01312e23          	sw	s3,28(sp)
   10a68:	01412c23          	sw	s4,24(sp)
   10a6c:	01612823          	sw	s6,16(sp)
   10a70:	01512a23          	sw	s5,20(sp)
   10a74:	01712623          	sw	s7,12(sp)
   10a78:	01812423          	sw	s8,8(sp)
   10a7c:	00058b13          	mv	s6,a1
   10a80:	0006a583          	lw	a1,0(a3)
   10a84:	00060b93          	mv	s7,a2
   10a88:	000b2603          	lw	a2,0(s6)
   10a8c:	00050a93          	mv	s5,a0
   10a90:	000b8513          	mv	a0,s7
   10a94:	00068a13          	mv	s4,a3
   10a98:	02b507b3          	mul	a5,a0,a1
   10a9c:	02b535b3          	mulhu	a1,a0,a1
   10aa0:	00c78533          	add	a0,a5,a2
   10aa4:	00f537b3          	sltu	a5,a0,a5
   10aa8:	00f585b3          	add	a1,a1,a5
   10aac:	03550ab3          	mul	s5,a0,s5
   10ab0:	00011c37          	lui	s8,0x11
   10ab4:	618c0c13          	addi	s8,s8,1560 # 11618 <__errno+0x2ec>
   10ab8:	00058413          	mv	s0,a1
   10abc:	000c2583          	lw	a1,0(s8)
   10ac0:	00050613          	mv	a2,a0
   10ac4:	004c0913          	addi	s2,s8,4
   10ac8:	004a0a13          	addi	s4,s4,4
   10acc:	000b0993          	mv	s3,s6
   10ad0:	180c0c13          	addi	s8,s8,384
   10ad4:	000a8513          	mv	a0,s5
   10ad8:	02b507b3          	mul	a5,a0,a1
   10adc:	02b535b3          	mulhu	a1,a0,a1
   10ae0:	00c78533          	add	a0,a5,a2
   10ae4:	00f537b3          	sltu	a5,a0,a5
   10ae8:	00f585b3          	add	a1,a1,a5
   10aec:	00058d93          	mv	s11,a1

00010af0 <w_start13>:
   10af0:	09895063          	bge	s2,s8,10b70 <w_end13>
   10af4:	0049a603          	lw	a2,4(s3)
   10af8:	000a2583          	lw	a1,0(s4)
   10afc:	00040693          	mv	a3,s0
   10b00:	000b8513          	mv	a0,s7
   10b04:	02b507b3          	mul	a5,a0,a1
   10b08:	02b535b3          	mulhu	a1,a0,a1
   10b0c:	00c78533          	add	a0,a5,a2
   10b10:	00f537b3          	sltu	a5,a0,a5
   10b14:	00f585b3          	add	a1,a1,a5
   10b18:	00d50533          	add	a0,a0,a3
   10b1c:	00d537b3          	sltu	a5,a0,a3
   10b20:	00f585b3          	add	a1,a1,a5
   10b24:	00058413          	mv	s0,a1
   10b28:	00092583          	lw	a1,0(s2)
   10b2c:	00050613          	mv	a2,a0
   10b30:	000d8693          	mv	a3,s11
   10b34:	000a8513          	mv	a0,s5
   10b38:	02b507b3          	mul	a5,a0,a1
   10b3c:	02b535b3          	mulhu	a1,a0,a1
   10b40:	00c78533          	add	a0,a5,a2
   10b44:	00f537b3          	sltu	a5,a0,a5
   10b48:	00f585b3          	add	a1,a1,a5
   10b4c:	00d50533          	add	a0,a0,a3
   10b50:	00d537b3          	sltu	a5,a0,a3
   10b54:	00f585b3          	add	a1,a1,a5
   10b58:	00a9a023          	sw	a0,0(s3)
   10b5c:	00490913          	addi	s2,s2,4
   10b60:	00058d93          	mv	s11,a1
   10b64:	004a0a13          	addi	s4,s4,4
   10b68:	00498993          	addi	s3,s3,4
   10b6c:	f85ff06f          	j	10af0 <w_start13>

00010b70 <w_end13>:
   10b70:	01b40433          	add	s0,s0,s11
   10b74:	0089a023          	sw	s0,0(s3)
   10b78:	01b44463          	blt	s0,s11,10b80 <if_true14>
   10b7c:	0540006f          	j	10bd0 <if_end14>

00010b80 <if_true14>:
   10b80:	000b0513          	mv	a0,s6
   10b84:	00011637          	lui	a2,0x11
   10b88:	61860613          	addi	a2,a2,1560 # 11618 <__errno+0x2ec>
   10b8c:	18060813          	addi	a6,a2,384
   10b90:	00000793          	li	a5,0
   10b94:	00000593          	li	a1,0

00010b98 <w_start15>:
   10b98:	03060c63          	beq	a2,a6,10bd0 <if_end14>
   10b9c:	00052703          	lw	a4,0(a0)
   10ba0:	00062683          	lw	a3,0(a2)
   10ba4:	00460613          	addi	a2,a2,4
   10ba8:	00e787b3          	add	a5,a5,a4
   10bac:	40d786b3          	sub	a3,a5,a3
   10bb0:	00e7b733          	sltu	a4,a5,a4
   10bb4:	00b70733          	add	a4,a4,a1
   10bb8:	00d7b7b3          	sltu	a5,a5,a3
   10bbc:	00d52023          	sw	a3,0(a0)
   10bc0:	00450513          	addi	a0,a0,4
   10bc4:	40f707b3          	sub	a5,a4,a5
   10bc8:	41f7d593          	srai	a1,a5,0x1f
   10bcc:	fcdff06f          	j	10b98 <w_start15>

00010bd0 <if_end14>:
   10bd0:	02c12083          	lw	ra,44(sp)
   10bd4:	02812403          	lw	s0,40(sp)
   10bd8:	02412d83          	lw	s11,36(sp)
   10bdc:	02012903          	lw	s2,32(sp)
   10be0:	01c12983          	lw	s3,28(sp)
   10be4:	01812a03          	lw	s4,24(sp)
   10be8:	01412a83          	lw	s5,20(sp)
   10bec:	01012b03          	lw	s6,16(sp)
   10bf0:	00c12b83          	lw	s7,12(sp)
   10bf4:	00812c03          	lw	s8,8(sp)
   10bf8:	03010113          	addi	sp,sp,48
   10bfc:	00490913          	addi	s2,s2,4
   10c00:	e3dff06f          	j	10a3c <w_start12>

00010c04 <w_end12>:
   10c04:	01c12083          	lw	ra,28(sp)
   10c08:	01812403          	lw	s0,24(sp)
   10c0c:	01412d83          	lw	s11,20(sp)
   10c10:	01012903          	lw	s2,16(sp)
   10c14:	00c12983          	lw	s3,12(sp)
   10c18:	00812a03          	lw	s4,8(sp)
   10c1c:	02010113          	addi	sp,sp,32
   10c20:	fffd8d93          	addi	s11,s11,-1
   10c24:	b81ff06f          	j	107a4 <w_start5>

00010c28 <w_end5>:
   10c28:	00098513          	mv	a0,s3
   10c2c:	000a8693          	mv	a3,s5
   10c30:	00040613          	mv	a2,s0
   10c34:	000a0593          	mv	a1,s4
   10c38:	fe010113          	addi	sp,sp,-32
   10c3c:	00112e23          	sw	ra,28(sp)
   10c40:	00812c23          	sw	s0,24(sp)
   10c44:	01b12a23          	sw	s11,20(sp)
   10c48:	01212823          	sw	s2,16(sp)
   10c4c:	01312623          	sw	s3,12(sp)
   10c50:	01412423          	sw	s4,8(sp)
   10c54:	00050413          	mv	s0,a0
   10c58:	00058d93          	mv	s11,a1
   10c5c:	00060913          	mv	s2,a2
   10c60:	00068993          	mv	s3,a3
   10c64:	180d8a13          	addi	s4,s11,384

00010c68 <w_start16>:
   10c68:	014dd863          	bge	s11,s4,10c78 <w_end16>
   10c6c:	000da023          	sw	zero,0(s11)
   10c70:	004d8d93          	addi	s11,s11,4
   10c74:	ff5ff06f          	j	10c68 <w_start16>

00010c78 <w_end16>:
   10c78:	00058d93          	mv	s11,a1
   10c7c:	18090a13          	addi	s4,s2,384

00010c80 <w_start17>:
   10c80:	1d495463          	bge	s2,s4,10e48 <w_end17>
   10c84:	000d8593          	mv	a1,s11
   10c88:	00040513          	mv	a0,s0
   10c8c:	00098693          	mv	a3,s3
   10c90:	00092603          	lw	a2,0(s2)
   10c94:	fd010113          	addi	sp,sp,-48
   10c98:	02112623          	sw	ra,44(sp)
   10c9c:	02812423          	sw	s0,40(sp)
   10ca0:	03b12223          	sw	s11,36(sp)
   10ca4:	03212023          	sw	s2,32(sp)
   10ca8:	01312e23          	sw	s3,28(sp)
   10cac:	01412c23          	sw	s4,24(sp)
   10cb0:	01612823          	sw	s6,16(sp)
   10cb4:	01512a23          	sw	s5,20(sp)
   10cb8:	01712623          	sw	s7,12(sp)
   10cbc:	01812423          	sw	s8,8(sp)
   10cc0:	00058b13          	mv	s6,a1
   10cc4:	0006a583          	lw	a1,0(a3)
   10cc8:	00060b93          	mv	s7,a2
   10ccc:	000b2603          	lw	a2,0(s6)
   10cd0:	00050a93          	mv	s5,a0
   10cd4:	000b8513          	mv	a0,s7
   10cd8:	00068a13          	mv	s4,a3
   10cdc:	02b507b3          	mul	a5,a0,a1
   10ce0:	02b535b3          	mulhu	a1,a0,a1
   10ce4:	00c78533          	add	a0,a5,a2
   10ce8:	00f537b3          	sltu	a5,a0,a5
   10cec:	00f585b3          	add	a1,a1,a5
   10cf0:	03550ab3          	mul	s5,a0,s5
   10cf4:	00011c37          	lui	s8,0x11
   10cf8:	618c0c13          	addi	s8,s8,1560 # 11618 <__errno+0x2ec>
   10cfc:	00058413          	mv	s0,a1
   10d00:	000c2583          	lw	a1,0(s8)
   10d04:	00050613          	mv	a2,a0
   10d08:	004c0913          	addi	s2,s8,4
   10d0c:	004a0a13          	addi	s4,s4,4
   10d10:	000b0993          	mv	s3,s6
   10d14:	180c0c13          	addi	s8,s8,384
   10d18:	000a8513          	mv	a0,s5
   10d1c:	02b507b3          	mul	a5,a0,a1
   10d20:	02b535b3          	mulhu	a1,a0,a1
   10d24:	00c78533          	add	a0,a5,a2
   10d28:	00f537b3          	sltu	a5,a0,a5
   10d2c:	00f585b3          	add	a1,a1,a5
   10d30:	00058d93          	mv	s11,a1

00010d34 <w_start18>:
   10d34:	09895063          	bge	s2,s8,10db4 <w_end18>
   10d38:	0049a603          	lw	a2,4(s3)
   10d3c:	000a2583          	lw	a1,0(s4)
   10d40:	00040693          	mv	a3,s0
   10d44:	000b8513          	mv	a0,s7
   10d48:	02b507b3          	mul	a5,a0,a1
   10d4c:	02b535b3          	mulhu	a1,a0,a1
   10d50:	00c78533          	add	a0,a5,a2
   10d54:	00f537b3          	sltu	a5,a0,a5
   10d58:	00f585b3          	add	a1,a1,a5
   10d5c:	00d50533          	add	a0,a0,a3
   10d60:	00d537b3          	sltu	a5,a0,a3
   10d64:	00f585b3          	add	a1,a1,a5
   10d68:	00058413          	mv	s0,a1
   10d6c:	00092583          	lw	a1,0(s2)
   10d70:	00050613          	mv	a2,a0
   10d74:	000d8693          	mv	a3,s11
   10d78:	000a8513          	mv	a0,s5
   10d7c:	02b507b3          	mul	a5,a0,a1
   10d80:	02b535b3          	mulhu	a1,a0,a1
   10d84:	00c78533          	add	a0,a5,a2
   10d88:	00f537b3          	sltu	a5,a0,a5
   10d8c:	00f585b3          	add	a1,a1,a5
   10d90:	00d50533          	add	a0,a0,a3
   10d94:	00d537b3          	sltu	a5,a0,a3
   10d98:	00f585b3          	add	a1,a1,a5
   10d9c:	00a9a023          	sw	a0,0(s3)
   10da0:	00490913          	addi	s2,s2,4
   10da4:	00058d93          	mv	s11,a1
   10da8:	004a0a13          	addi	s4,s4,4
   10dac:	00498993          	addi	s3,s3,4
   10db0:	f85ff06f          	j	10d34 <w_start18>

00010db4 <w_end18>:
   10db4:	01b40433          	add	s0,s0,s11
   10db8:	0089a023          	sw	s0,0(s3)
   10dbc:	01b44463          	blt	s0,s11,10dc4 <if_true19>
   10dc0:	0540006f          	j	10e14 <if_end19>

00010dc4 <if_true19>:
   10dc4:	000b0513          	mv	a0,s6
   10dc8:	00011637          	lui	a2,0x11
   10dcc:	61860613          	addi	a2,a2,1560 # 11618 <__errno+0x2ec>
   10dd0:	18060813          	addi	a6,a2,384
   10dd4:	00000793          	li	a5,0
   10dd8:	00000593          	li	a1,0

00010ddc <w_start20>:
   10ddc:	03060c63          	beq	a2,a6,10e14 <if_end19>
   10de0:	00052703          	lw	a4,0(a0)
   10de4:	00062683          	lw	a3,0(a2)
   10de8:	00460613          	addi	a2,a2,4
   10dec:	00e787b3          	add	a5,a5,a4
   10df0:	40d786b3          	sub	a3,a5,a3
   10df4:	00e7b733          	sltu	a4,a5,a4
   10df8:	00b70733          	add	a4,a4,a1
   10dfc:	00d7b7b3          	sltu	a5,a5,a3
   10e00:	00d52023          	sw	a3,0(a0)
   10e04:	00450513          	addi	a0,a0,4
   10e08:	40f707b3          	sub	a5,a4,a5
   10e0c:	41f7d593          	srai	a1,a5,0x1f
   10e10:	fcdff06f          	j	10ddc <w_start20>

00010e14 <if_end19>:
   10e14:	02c12083          	lw	ra,44(sp)
   10e18:	02812403          	lw	s0,40(sp)
   10e1c:	02412d83          	lw	s11,36(sp)
   10e20:	02012903          	lw	s2,32(sp)
   10e24:	01c12983          	lw	s3,28(sp)
   10e28:	01812a03          	lw	s4,24(sp)
   10e2c:	01412a83          	lw	s5,20(sp)
   10e30:	01012b03          	lw	s6,16(sp)
   10e34:	00c12b83          	lw	s7,12(sp)
   10e38:	00812c03          	lw	s8,8(sp)
   10e3c:	03010113          	addi	sp,sp,48
   10e40:	00490913          	addi	s2,s2,4
   10e44:	e3dff06f          	j	10c80 <w_start17>

00010e48 <w_end17>:
   10e48:	01c12083          	lw	ra,28(sp)
   10e4c:	01812403          	lw	s0,24(sp)
   10e50:	01412d83          	lw	s11,20(sp)
   10e54:	01012903          	lw	s2,16(sp)
   10e58:	00c12983          	lw	s3,12(sp)
   10e5c:	00812a03          	lw	s4,8(sp)
   10e60:	02010113          	addi	sp,sp,32
   10e64:	000a0513          	mv	a0,s4
   10e68:	000115b7          	lui	a1,0x11
   10e6c:	61858793          	addi	a5,a1,1560 # 11618 <__errno+0x2ec>
   10e70:	17c50513          	addi	a0,a0,380
   10e74:	17c78793          	addi	a5,a5,380
   10e78:	61858593          	addi	a1,a1,1560
   10e7c:	00100613          	li	a2,1

00010e80 <w_start21>:
   10e80:	02060a63          	beqz	a2,10eb4 <w_end21>
   10e84:	00052683          	lw	a3,0(a0)
   10e88:	0007a703          	lw	a4,0(a5)
   10e8c:	40e68633          	sub	a2,a3,a4
   10e90:	00e6b6b3          	sltu	a3,a3,a4
   10e94:	00c03733          	snez	a4,a2
   10e98:	00f5c633          	xor	a2,a1,a5
   10e9c:	00071463          	bnez	a4,10ea4 <if_true22>
   10ea0:	0080006f          	j	10ea8 <if_end22>

00010ea4 <if_true22>:
   10ea4:	00000633          	add	a2,zero,zero

00010ea8 <if_end22>:
   10ea8:	ffc50513          	addi	a0,a0,-4
   10eac:	ffc78793          	addi	a5,a5,-4
   10eb0:	fd1ff06f          	j	10e80 <w_start21>

00010eb4 <w_end21>:
   10eb4:	00068513          	mv	a0,a3
   10eb8:	00050463          	beqz	a0,10ec0 <if_true23>
   10ebc:	0540006f          	j	10f10 <if_end23>

00010ec0 <if_true23>:
   10ec0:	000a0513          	mv	a0,s4
   10ec4:	00011637          	lui	a2,0x11
   10ec8:	61860613          	addi	a2,a2,1560 # 11618 <__errno+0x2ec>
   10ecc:	18060813          	addi	a6,a2,384
   10ed0:	00000793          	li	a5,0
   10ed4:	00000593          	li	a1,0

00010ed8 <w_start24>:
   10ed8:	03060c63          	beq	a2,a6,10f10 <if_end23>
   10edc:	00052703          	lw	a4,0(a0)
   10ee0:	00062683          	lw	a3,0(a2)
   10ee4:	00460613          	addi	a2,a2,4
   10ee8:	00e787b3          	add	a5,a5,a4
   10eec:	40d786b3          	sub	a3,a5,a3
   10ef0:	00e7b733          	sltu	a4,a5,a4
   10ef4:	00b70733          	add	a4,a4,a1
   10ef8:	00d7b7b3          	sltu	a5,a5,a3
   10efc:	00d52023          	sw	a3,0(a0)
   10f00:	00450513          	addi	a0,a0,4
   10f04:	40f707b3          	sub	a5,a4,a5
   10f08:	41f7d593          	srai	a1,a5,0x1f
   10f0c:	fcdff06f          	j	10ed8 <w_start24>

00010f10 <if_end23>:
   10f10:	01c12083          	lw	ra,28(sp)
   10f14:	01812403          	lw	s0,24(sp)
   10f18:	01412d83          	lw	s11,20(sp)
   10f1c:	01012903          	lw	s2,16(sp)
   10f20:	00c12983          	lw	s3,12(sp)
   10f24:	00812a03          	lw	s4,8(sp)
   10f28:	00412a83          	lw	s5,4(sp)
   10f2c:	02010113          	addi	sp,sp,32
   10f30:	00008067          	ret

00010f34 <exit>:
   10f34:	ff010113          	addi	sp,sp,-16
   10f38:	00000593          	li	a1,0
   10f3c:	00812423          	sw	s0,8(sp)
   10f40:	00112623          	sw	ra,12(sp)
   10f44:	00050413          	mv	s0,a0
   10f48:	18c000ef          	jal	ra,110d4 <__call_exitprocs>
   10f4c:	0a81a503          	lw	a0,168(gp) # 12bf0 <_global_impure_ptr>
   10f50:	03c52783          	lw	a5,60(a0)
   10f54:	00078463          	beqz	a5,10f5c <exit+0x28>
   10f58:	000780e7          	jalr	a5
   10f5c:	00040513          	mv	a0,s0
   10f60:	39c000ef          	jal	ra,112fc <_exit>

00010f64 <__libc_init_array>:
   10f64:	ff010113          	addi	sp,sp,-16
   10f68:	00812423          	sw	s0,8(sp)
   10f6c:	01212023          	sw	s2,0(sp)
   10f70:	00001417          	auipc	s0,0x1
   10f74:	3c840413          	addi	s0,s0,968 # 12338 <__init_array_start>
   10f78:	00001917          	auipc	s2,0x1
   10f7c:	3c090913          	addi	s2,s2,960 # 12338 <__init_array_start>
   10f80:	40890933          	sub	s2,s2,s0
   10f84:	00112623          	sw	ra,12(sp)
   10f88:	00912223          	sw	s1,4(sp)
   10f8c:	40295913          	srai	s2,s2,0x2
   10f90:	00090e63          	beqz	s2,10fac <__libc_init_array+0x48>
   10f94:	00000493          	li	s1,0
   10f98:	00042783          	lw	a5,0(s0)
   10f9c:	00148493          	addi	s1,s1,1
   10fa0:	00440413          	addi	s0,s0,4
   10fa4:	000780e7          	jalr	a5
   10fa8:	fe9918e3          	bne	s2,s1,10f98 <__libc_init_array+0x34>
   10fac:	00001417          	auipc	s0,0x1
   10fb0:	38c40413          	addi	s0,s0,908 # 12338 <__init_array_start>
   10fb4:	00001917          	auipc	s2,0x1
   10fb8:	38c90913          	addi	s2,s2,908 # 12340 <__do_global_dtors_aux_fini_array_entry>
   10fbc:	40890933          	sub	s2,s2,s0
   10fc0:	40295913          	srai	s2,s2,0x2
   10fc4:	00090e63          	beqz	s2,10fe0 <__libc_init_array+0x7c>
   10fc8:	00000493          	li	s1,0
   10fcc:	00042783          	lw	a5,0(s0)
   10fd0:	00148493          	addi	s1,s1,1
   10fd4:	00440413          	addi	s0,s0,4
   10fd8:	000780e7          	jalr	a5
   10fdc:	fe9918e3          	bne	s2,s1,10fcc <__libc_init_array+0x68>
   10fe0:	00c12083          	lw	ra,12(sp)
   10fe4:	00812403          	lw	s0,8(sp)
   10fe8:	00412483          	lw	s1,4(sp)
   10fec:	00012903          	lw	s2,0(sp)
   10ff0:	01010113          	addi	sp,sp,16
   10ff4:	00008067          	ret

00010ff8 <memset>:
   10ff8:	00f00313          	li	t1,15
   10ffc:	00050713          	mv	a4,a0
   11000:	02c37e63          	bgeu	t1,a2,1103c <memset+0x44>
   11004:	00f77793          	andi	a5,a4,15
   11008:	0a079063          	bnez	a5,110a8 <memset+0xb0>
   1100c:	08059263          	bnez	a1,11090 <memset+0x98>
   11010:	ff067693          	andi	a3,a2,-16
   11014:	00f67613          	andi	a2,a2,15
   11018:	00e686b3          	add	a3,a3,a4
   1101c:	00b72023          	sw	a1,0(a4)
   11020:	00b72223          	sw	a1,4(a4)
   11024:	00b72423          	sw	a1,8(a4)
   11028:	00b72623          	sw	a1,12(a4)
   1102c:	01070713          	addi	a4,a4,16
   11030:	fed766e3          	bltu	a4,a3,1101c <memset+0x24>
   11034:	00061463          	bnez	a2,1103c <memset+0x44>
   11038:	00008067          	ret
   1103c:	40c306b3          	sub	a3,t1,a2
   11040:	00269693          	slli	a3,a3,0x2
   11044:	00000297          	auipc	t0,0x0
   11048:	005686b3          	add	a3,a3,t0
   1104c:	00c68067          	jr	12(a3)
   11050:	00b70723          	sb	a1,14(a4)
   11054:	00b706a3          	sb	a1,13(a4)
   11058:	00b70623          	sb	a1,12(a4)
   1105c:	00b705a3          	sb	a1,11(a4)
   11060:	00b70523          	sb	a1,10(a4)
   11064:	00b704a3          	sb	a1,9(a4)
   11068:	00b70423          	sb	a1,8(a4)
   1106c:	00b703a3          	sb	a1,7(a4)
   11070:	00b70323          	sb	a1,6(a4)
   11074:	00b702a3          	sb	a1,5(a4)
   11078:	00b70223          	sb	a1,4(a4)
   1107c:	00b701a3          	sb	a1,3(a4)
   11080:	00b70123          	sb	a1,2(a4)
   11084:	00b700a3          	sb	a1,1(a4)
   11088:	00b70023          	sb	a1,0(a4)
   1108c:	00008067          	ret
   11090:	0ff5f593          	zext.b	a1,a1
   11094:	00859693          	slli	a3,a1,0x8
   11098:	00d5e5b3          	or	a1,a1,a3
   1109c:	01059693          	slli	a3,a1,0x10
   110a0:	00d5e5b3          	or	a1,a1,a3
   110a4:	f6dff06f          	j	11010 <memset+0x18>
   110a8:	00279693          	slli	a3,a5,0x2
   110ac:	00000297          	auipc	t0,0x0
   110b0:	005686b3          	add	a3,a3,t0
   110b4:	00008293          	mv	t0,ra
   110b8:	fa0680e7          	jalr	-96(a3)
   110bc:	00028093          	mv	ra,t0
   110c0:	ff078793          	addi	a5,a5,-16
   110c4:	40f70733          	sub	a4,a4,a5
   110c8:	00f60633          	add	a2,a2,a5
   110cc:	f6c378e3          	bgeu	t1,a2,1103c <memset+0x44>
   110d0:	f3dff06f          	j	1100c <memset+0x14>

000110d4 <__call_exitprocs>:
   110d4:	fd010113          	addi	sp,sp,-48
   110d8:	01412c23          	sw	s4,24(sp)
   110dc:	0a81aa03          	lw	s4,168(gp) # 12bf0 <_global_impure_ptr>
   110e0:	03212023          	sw	s2,32(sp)
   110e4:	148a2903          	lw	s2,328(s4)
   110e8:	02112623          	sw	ra,44(sp)
   110ec:	02812423          	sw	s0,40(sp)
   110f0:	02912223          	sw	s1,36(sp)
   110f4:	01312e23          	sw	s3,28(sp)
   110f8:	01512a23          	sw	s5,20(sp)
   110fc:	01612823          	sw	s6,16(sp)
   11100:	01712623          	sw	s7,12(sp)
   11104:	01812423          	sw	s8,8(sp)
   11108:	04090063          	beqz	s2,11148 <__call_exitprocs+0x74>
   1110c:	00050b13          	mv	s6,a0
   11110:	00058b93          	mv	s7,a1
   11114:	00100a93          	li	s5,1
   11118:	fff00993          	li	s3,-1
   1111c:	00492483          	lw	s1,4(s2)
   11120:	fff48413          	addi	s0,s1,-1
   11124:	02044263          	bltz	s0,11148 <__call_exitprocs+0x74>
   11128:	00249493          	slli	s1,s1,0x2
   1112c:	009904b3          	add	s1,s2,s1
   11130:	040b8463          	beqz	s7,11178 <__call_exitprocs+0xa4>
   11134:	1044a783          	lw	a5,260(s1)
   11138:	05778063          	beq	a5,s7,11178 <__call_exitprocs+0xa4>
   1113c:	fff40413          	addi	s0,s0,-1
   11140:	ffc48493          	addi	s1,s1,-4
   11144:	ff3416e3          	bne	s0,s3,11130 <__call_exitprocs+0x5c>
   11148:	02c12083          	lw	ra,44(sp)
   1114c:	02812403          	lw	s0,40(sp)
   11150:	02412483          	lw	s1,36(sp)
   11154:	02012903          	lw	s2,32(sp)
   11158:	01c12983          	lw	s3,28(sp)
   1115c:	01812a03          	lw	s4,24(sp)
   11160:	01412a83          	lw	s5,20(sp)
   11164:	01012b03          	lw	s6,16(sp)
   11168:	00c12b83          	lw	s7,12(sp)
   1116c:	00812c03          	lw	s8,8(sp)
   11170:	03010113          	addi	sp,sp,48
   11174:	00008067          	ret
   11178:	00492783          	lw	a5,4(s2)
   1117c:	0044a683          	lw	a3,4(s1)
   11180:	fff78793          	addi	a5,a5,-1
   11184:	04878e63          	beq	a5,s0,111e0 <__call_exitprocs+0x10c>
   11188:	0004a223          	sw	zero,4(s1)
   1118c:	fa0688e3          	beqz	a3,1113c <__call_exitprocs+0x68>
   11190:	18892783          	lw	a5,392(s2)
   11194:	008a9733          	sll	a4,s5,s0
   11198:	00492c03          	lw	s8,4(s2)
   1119c:	00f777b3          	and	a5,a4,a5
   111a0:	02079263          	bnez	a5,111c4 <__call_exitprocs+0xf0>
   111a4:	000680e7          	jalr	a3
   111a8:	00492703          	lw	a4,4(s2)
   111ac:	148a2783          	lw	a5,328(s4)
   111b0:	01871463          	bne	a4,s8,111b8 <__call_exitprocs+0xe4>
   111b4:	f92784e3          	beq	a5,s2,1113c <__call_exitprocs+0x68>
   111b8:	f80788e3          	beqz	a5,11148 <__call_exitprocs+0x74>
   111bc:	00078913          	mv	s2,a5
   111c0:	f5dff06f          	j	1111c <__call_exitprocs+0x48>
   111c4:	18c92783          	lw	a5,396(s2)
   111c8:	0844a583          	lw	a1,132(s1)
   111cc:	00f77733          	and	a4,a4,a5
   111d0:	00071c63          	bnez	a4,111e8 <__call_exitprocs+0x114>
   111d4:	000b0513          	mv	a0,s6
   111d8:	000680e7          	jalr	a3
   111dc:	fcdff06f          	j	111a8 <__call_exitprocs+0xd4>
   111e0:	00892223          	sw	s0,4(s2)
   111e4:	fa9ff06f          	j	1118c <__call_exitprocs+0xb8>
   111e8:	00058513          	mv	a0,a1
   111ec:	000680e7          	jalr	a3
   111f0:	fb9ff06f          	j	111a8 <__call_exitprocs+0xd4>

000111f4 <atexit>:
   111f4:	00050593          	mv	a1,a0
   111f8:	00000693          	li	a3,0
   111fc:	00000613          	li	a2,0
   11200:	00000513          	li	a0,0
   11204:	0600006f          	j	11264 <__register_exitproc>

00011208 <__libc_fini_array>:
   11208:	ff010113          	addi	sp,sp,-16
   1120c:	00812423          	sw	s0,8(sp)
   11210:	00001797          	auipc	a5,0x1
   11214:	13078793          	addi	a5,a5,304 # 12340 <__do_global_dtors_aux_fini_array_entry>
   11218:	00001417          	auipc	s0,0x1
   1121c:	12c40413          	addi	s0,s0,300 # 12344 <__fini_array_end>
   11220:	40f40433          	sub	s0,s0,a5
   11224:	00912223          	sw	s1,4(sp)
   11228:	00112623          	sw	ra,12(sp)
   1122c:	40245493          	srai	s1,s0,0x2
   11230:	02048063          	beqz	s1,11250 <__libc_fini_array+0x48>
   11234:	ffc40413          	addi	s0,s0,-4
   11238:	00f40433          	add	s0,s0,a5
   1123c:	00042783          	lw	a5,0(s0)
   11240:	fff48493          	addi	s1,s1,-1
   11244:	ffc40413          	addi	s0,s0,-4
   11248:	000780e7          	jalr	a5
   1124c:	fe0498e3          	bnez	s1,1123c <__libc_fini_array+0x34>
   11250:	00c12083          	lw	ra,12(sp)
   11254:	00812403          	lw	s0,8(sp)
   11258:	00412483          	lw	s1,4(sp)
   1125c:	01010113          	addi	sp,sp,16
   11260:	00008067          	ret

00011264 <__register_exitproc>:
   11264:	0a81a703          	lw	a4,168(gp) # 12bf0 <_global_impure_ptr>
   11268:	14872783          	lw	a5,328(a4)
   1126c:	04078c63          	beqz	a5,112c4 <__register_exitproc+0x60>
   11270:	0047a703          	lw	a4,4(a5)
   11274:	01f00813          	li	a6,31
   11278:	06e84e63          	blt	a6,a4,112f4 <__register_exitproc+0x90>
   1127c:	00271813          	slli	a6,a4,0x2
   11280:	02050663          	beqz	a0,112ac <__register_exitproc+0x48>
   11284:	01078333          	add	t1,a5,a6
   11288:	08c32423          	sw	a2,136(t1) # 1022c <sub_mod.constprop.0+0x34>
   1128c:	1887a883          	lw	a7,392(a5)
   11290:	00100613          	li	a2,1
   11294:	00e61633          	sll	a2,a2,a4
   11298:	00c8e8b3          	or	a7,a7,a2
   1129c:	1917a423          	sw	a7,392(a5)
   112a0:	10d32423          	sw	a3,264(t1)
   112a4:	00200693          	li	a3,2
   112a8:	02d50463          	beq	a0,a3,112d0 <__register_exitproc+0x6c>
   112ac:	00170713          	addi	a4,a4,1
   112b0:	00e7a223          	sw	a4,4(a5)
   112b4:	010787b3          	add	a5,a5,a6
   112b8:	00b7a423          	sw	a1,8(a5)
   112bc:	00000513          	li	a0,0
   112c0:	00008067          	ret
   112c4:	14c70793          	addi	a5,a4,332
   112c8:	14f72423          	sw	a5,328(a4)
   112cc:	fa5ff06f          	j	11270 <__register_exitproc+0xc>
   112d0:	18c7a683          	lw	a3,396(a5)
   112d4:	00170713          	addi	a4,a4,1
   112d8:	00e7a223          	sw	a4,4(a5)
   112dc:	00c6e6b3          	or	a3,a3,a2
   112e0:	18d7a623          	sw	a3,396(a5)
   112e4:	010787b3          	add	a5,a5,a6
   112e8:	00b7a423          	sw	a1,8(a5)
   112ec:	00000513          	li	a0,0
   112f0:	00008067          	ret
   112f4:	fff00513          	li	a0,-1
   112f8:	00008067          	ret

000112fc <_exit>:
   112fc:	05d00893          	li	a7,93
   11300:	00000073          	ecall
   11304:	00054463          	bltz	a0,1130c <_exit+0x10>
   11308:	0000006f          	j	11308 <_exit+0xc>
   1130c:	ff010113          	addi	sp,sp,-16
   11310:	00812423          	sw	s0,8(sp)
   11314:	00050413          	mv	s0,a0
   11318:	00112623          	sw	ra,12(sp)
   1131c:	40800433          	neg	s0,s0
   11320:	00c000ef          	jal	ra,1132c <__errno>
   11324:	00852023          	sw	s0,0(a0)
   11328:	0000006f          	j	11328 <_exit+0x2c>

0001132c <__errno>:
   1132c:	0b41a503          	lw	a0,180(gp) # 12bfc <_impure_ptr>
   11330:	00008067          	ret

Disassembly of section .eh_frame:

00012334 <__FRAME_END__>:
   12334:	0000                	unimp
	...

Disassembly of section .init_array:

00012338 <__init_array_start>:
   12338:	00e4                	addi	s1,sp,76
   1233a:	0001                	nop

0001233c <__frame_dummy_init_array_entry>:
   1233c:	0190                	addi	a2,sp,192
   1233e:	0001                	nop

Disassembly of section .fini_array:

00012340 <__do_global_dtors_aux_fini_array_entry>:
   12340:	0148                	addi	a0,sp,132
   12342:	0001                	nop

Disassembly of section .data:

00012348 <n>:
   12348:	75e1                	lui	a1,0xffff8
   1234a:	6a6a                	flw	fs4,152(sp)
   1234c:	ddc5                	beqz	a1,12304 <__errno+0xfd8>
   1234e:	a018                	fsd	fa4,0(s0)
   12350:	b168                	fsd	fa0,224(a0)
   12352:	05a5687b          	0x5a5687b
   12356:	8e82                	jr	t4
   12358:	7dbfffa7          	0x7dbfffa7
   1235c:	2ac5                	jal	1254c <rr+0x84>
   1235e:	c872                	sw	t3,16(sp)
   12360:	f84d21cf          	fnmadd.s	ft3,fs10,ft4,ft11,rdn
   12364:	2531                	jal	12970 <impure_data+0x1a8>
   12366:	e131                	bnez	a0,123aa <n+0x62>
   12368:	0ce3f8a3          	0xce3f8a3
   1236c:	f988                	fsw	fa0,48(a1)
   1236e:	a825                	j	123a6 <n+0x5e>
   12370:	1964                	addi	s1,sp,188
   12372:	57f5                	li	a5,-3
   12374:	206a                	fld	ft0,152(sp)
   12376:	b27e                	fsd	ft11,288(sp)
   12378:	d008                	sw	a0,32(s0)
   1237a:	8e1d                	sub	a2,a2,a5
   1237c:	1c4fb8d7          	0x1c4fb8d7
   12380:	b142                	fsd	fa6,160(sp)
   12382:	e7b3824f          	fnmadd.q	ft4,ft7,fs11,ft8,rne
   12386:	63661c8b          	0x63661c8b
   1238a:	7b9d                	lui	s7,0xfffe7
   1238c:	d0f2                	sw	t3,96(sp)
   1238e:	c56a                	sw	s10,136(sp)
   12390:	ef762d5b          	0xef762d5b
   12394:	4b1431e3          	0x4b1431e3
   12398:	8eb9                	xor	a3,a3,a4
   1239a:	8ae2                	mv	s5,s8
   1239c:	b7aa                	fsd	fa0,488(sp)
   1239e:	d41d                	beqz	s0,122cc <__errno+0xfa0>
   123a0:	43cccdf7          	0x43cccdf7
   123a4:	4a84                	lw	s1,16(a3)
   123a6:	385091b7          	lui	gp,0x38509
   123aa:	8018                	0x8018
   123ac:	4d0d                	li	s10,3
   123ae:	d01530e7          	0xd01530e7
   123b2:	b62e                	fsd	fa1,296(sp)
   123b4:	74d2                	flw	fs1,52(sp)
   123b6:	2355                	jal	1295a <impure_data+0x192>
   123b8:	f251                	bnez	a2,1233c <__frame_dummy_init_array_entry>
   123ba:	8c28                	0x8c28
   123bc:	def2                	sw	t3,124(sp)
   123be:	4f40                	lw	s0,28(a4)
   123c0:	24e2efdb          	0x24e2efdb
   123c4:	1ff2                	slli	t6,t6,0x3c
   123c6:	9ebd                	0x9ebd
   123c8:	49ee                	lw	s3,216(sp)
   123ca:	a938fa7b          	0xa938fa7b
   123ce:	2819                	jal	123e4 <n+0x9c>
   123d0:	b8c8                	fsd	fa0,176(s1)
   123d2:	6e66                	flw	ft8,88(sp)
   123d4:	1546                	slli	a0,a0,0x31
   123d6:	24e4                	fld	fs1,200(s1)
   123d8:	3a7c                	fld	fa5,240(a2)
   123da:	4d78                	lw	a4,92(a0)
   123dc:	7d3d                	lui	s10,0xfffef
   123de:	d294                	sw	a3,32(a3)
   123e0:	69e9                	lui	s3,0x1a
   123e2:	1ab2                	slli	s5,s5,0x2c
   123e4:	9f16                	add	t5,t5,t0
   123e6:	8f7bfad3          	0x8f7bfad3
   123ea:	b510aab7          	lui	s5,0xb510a
   123ee:	49d8                	lw	a4,20(a1)
   123f0:	35bf0dfb          	0x35bf0dfb
   123f4:	4754                	lw	a3,12(a4)
   123f6:	ccc9eb27          	0xccc9eb27
   123fa:	069e                	slli	a3,a3,0x7
   123fc:	437e                	lw	t1,220(sp)
   123fe:	c13c                	sw	a5,64(a0)
   12400:	0f60                	addi	s0,sp,924
   12402:	e3bc                	fsw	fa5,64(a5)
   12404:	c9e0e12f          	0xc9e0e12f
   12408:	c253ac43          	fmadd.d	fs8,ft7,ft5,fs8,rdn
   1240c:	40e0                	lw	s0,68(s1)
   1240e:	89c2                	mv	s3,a6
   12410:	a4e5                	j	126f8 <sig+0xb0>
   12412:	4bc0c4ab          	0x4bc0c4ab
   12416:	c462edf3          	csrrsi	s11,0xc46,5
   1241a:	5402                	lw	s0,32(sp)
   1241c:	b0bd                	j	11c8a <__errno+0x95e>
   1241e:	4021                	c.li	zero,8
   12420:	6241                	lui	tp,0x10
   12422:	945f996b          	0x945f996b
   12426:	c3d9                	beqz	a5,124ac <n+0x164>
   12428:	ac60                	fsd	fs0,216(s0)
   1242a:	0bf5a137          	lui	sp,0xbf5a
   1242e:	f025                	bnez	s0,1238e <n+0x46>
   12430:	c8c7100f          	0xc8c7100f
   12434:	6b88                	flw	fa0,16(a5)
   12436:	b70d                	j	12358 <n+0x10>
   12438:	6a8c                	flw	fa1,16(a3)
   1243a:	7891                	lui	a7,0xfffe4
   1243c:	0e5d                	addi	t3,t3,23
   1243e:	dcb93337          	lui	t1,0xdcb93
   12442:	3970                	fld	fa2,240(a0)
   12444:	58b4                	lw	a3,112(s1)
   12446:	af4c                	fsd	fa1,152(a4)
   12448:	cb0d                	beqz	a4,1247a <n+0x132>
   1244a:	5f78                	lw	a4,124(a4)
   1244c:	b02d90b7          	lui	ra,0xb02d9
   12450:	3d05                	jal	12280 <__errno+0xf54>
   12452:	eb6c                	fsw	fa1,84(a4)
   12454:	c71a                	sw	t1,140(sp)
   12456:	5f0f04af          	0x5f0f04af
   1245a:	4518                	lw	a4,8(a0)
   1245c:	987caa5b          	0x987caa5b
   12460:	6249                	lui	tp,0x12
   12462:	fdbc3397          	auipc	t2,0xfdbc3
   12466:	565a                	lw	a2,180(sp)
   12468:	5056                	0x5056
   1246a:	80a8                	0x80a8
   1246c:	7655                	lui	a2,0xffff5
   1246e:	59e0                	lw	s0,116(a1)
   12470:	e77d                	bnez	a4,1255e <rr+0x96>
   12472:	9a29                	andi	a2,a2,-22
   12474:	fb7f                	0xfb7f
   12476:	7a8d                	lui	s5,0xfffe3
   12478:	0204                	addi	s1,sp,256
   1247a:	782e                	flw	fa6,232(sp)
   1247c:	13ff                	0x13ff
   1247e:	00ea4d67          	0xea4d67
   12482:	1310                	addi	a2,sp,416
   12484:	1206                	slli	tp,tp,0x21
   12486:	e18e                	fsw	ft3,192(sp)
   12488:	7f30                	flw	fa2,120(a4)
   1248a:	21f5                	jal	12976 <impure_data+0x1ae>
   1248c:	f24f038b          	0xf24f038b
   12490:	874d                	srai	a4,a4,0x13
   12492:	052559cf          	0x52559cf
   12496:	24c5                	jal	12776 <sig+0x12e>
   12498:	170d                	addi	a4,a4,-29
   1249a:	addeb52f          	0xaddeb52f
   1249e:	46c9                	li	a3,18
   124a0:	90e82c73          	csrrs	s8,0x90e,a6
   124a4:	1344ceaf          	0x1344ceaf
   124a8:	09f2                	slli	s3,s3,0x1c
   124aa:	6632                	flw	fa2,12(sp)
   124ac:	24bd4fbf 5e4ed04d 	0x5e4ed04d24bd4fbf
   124b4:	770a                	flw	fa4,160(sp)
   124b6:	0fce                	slli	t6,t6,0x13
   124b8:	81f78793          	addi	a5,a5,-2017
   124bc:	e13e                	fsw	fa5,128(sp)
   124be:	a792                	fsd	ft4,456(sp)
   124c0:	bf58                	fsd	fa4,184(a4)
   124c2:	9be8a6c7          	fmsub.d	fa3,fa7,ft10,fs3,rdn
   124c6:	e1df        	0xa3eb77fae1df

000124c8 <rr>:
   124c8:	77fa                	flw	fa5,188(sp)
   124ca:	a2aca3eb          	0xa2aca3eb
   124ce:	9db9                	0x9db9
   124d0:	d4ae                	sw	a1,104(sp)
   124d2:	2c19                	jal	126e8 <sig+0xa0>
   124d4:	fb5be1e7          	0xfb5be1e7
   124d8:	dd38f5fb          	0xdd38f5fb
   124dc:	fdda                	fsw	fs6,248(sp)
   124de:	d0f4                	sw	a3,100(s1)
   124e0:	eb165cd3          	0xeb165cd3
   124e4:	7cfe                	flw	fs9,252(sp)
   124e6:	546a                	lw	s0,184(sp)
   124e8:	0c5c                	addi	a5,sp,532
   124ea:	cd41                	beqz	a0,12582 <rr+0xba>
   124ec:	73f5cf6b          	0x73f5cf6b
   124f0:	bcae                	fsd	fa1,120(sp)
   124f2:	1185                	addi	gp,gp,-31
   124f4:	da2e2103          	lw	sp,-606(t3)
   124f8:	ae26                	fsd	fs1,280(sp)
   124fa:	bab5                	j	11e76 <__errno+0xb4a>
   124fc:	7aba                	flw	fs5,172(sp)
   124fe:	d5f776e7          	0xd5f776e7
   12502:	f49d                	bnez	s1,12430 <n+0xe8>
   12504:	8a29                	andi	a2,a2,10
   12506:	3231                	jal	11e12 <__errno+0xae6>
   12508:	85bc                	0x85bc
   1250a:	689a                	flw	fa7,132(sp)
   1250c:	62a9                	lui	t0,0xa
   1250e:	8aa8                	0x8aa8
   12510:	240e                	fld	fs0,192(sp)
   12512:	538c                	lw	a1,32(a5)
   12514:	b61eab77          	0xb61eab77
   12518:	73f2                	flw	ft7,60(sp)
   1251a:	9ccd                	0x9ccd
   1251c:	c81a                	sw	t1,16(sp)
   1251e:	ac0e6563          	bltu	t3,zero,117e8 <__errno+0x4bc>
   12522:	6c65                	lui	s8,0x19
   12524:	90b209bf e642e25e 	0xe642e25e90b209bf
   1252c:	1549                	addi	a0,a0,-14
   1252e:	7e35                	lui	t3,0xfffed
   12530:	1830                	addi	a2,sp,56
   12532:	879a                	mv	a5,t1
   12534:	bb02                	fsd	ft0,432(sp)
   12536:	c75c                	sw	a5,12(a4)
   12538:	2362                	fld	ft6,24(sp)
   1253a:	e011                	bnez	s0,1253e <rr+0x76>
   1253c:	405f ebc2 7990      	0x7990ebc2405f
   12542:	01dc                	addi	a5,sp,196
   12544:	3d3d07f3          	0x3d3d07f3
   12548:	a5be                	fsd	fa5,200(sp)
   1254a:	c5b9                	beqz	a1,12598 <rr+0xd0>
   1254c:	98d8cc33          	0x98d8cc33
   12550:	e108                	fsw	fa0,0(a0)
   12552:	dd65                	beqz	a0,1254a <rr+0x82>
   12554:	ce301343          	fmadd.q	ft6,ft0,ft3,fs9,rtz
   12558:	0dbdc0cb          	0xdbdc0cb
   1255c:	b9ca                	fsd	fs2,240(sp)
   1255e:	c204                	sw	s1,0(a2)
   12560:	1810                	addi	a2,sp,48
   12562:	eabe                	fsw	fa5,84(sp)
   12564:	163a                	slli	a2,a2,0x2e
   12566:	9849                	andi	s0,s0,-14
   12568:	234c8ff7          	0x234c8ff7
   1256c:	9bc14e3b          	0x9bc14e3b
   12570:	2226                	fld	ft4,72(sp)
   12572:	4b4c                	lw	a1,20(a4)
   12574:	83be                	mv	t2,a5
   12576:	0798                	addi	a4,sp,960
   12578:	c5f5                	beqz	a1,12664 <sig+0x1c>
   1257a:	ba59                	j	11f10 <__errno+0xbe4>
   1257c:	d9c77317          	auipc	t1,0xd9c77
   12580:	89f5                	andi	a1,a1,29
   12582:	1ce6                	slli	s9,s9,0x39
   12584:	9af5                	andi	a3,a3,-3
   12586:	05f4                	addi	a3,sp,716
   12588:	d42a                	sw	a0,40(sp)
   1258a:	b5ca7a83          	0xb5ca7a83
   1258e:	c509                	beqz	a0,12598 <rr+0xd0>
   12590:	a95f 0811 20a2      	0x20a20811a95f
   12596:	0935                	addi	s2,s2,13
   12598:	9941                	andi	a0,a0,-16
   1259a:	7364                	flw	fs1,100(a4)
   1259c:	1ef5                	addi	t4,t4,-3
   1259e:	d969                	beqz	a0,12570 <rr+0xa8>
   125a0:	ec0d                	bnez	s0,125da <rr+0x112>
   125a2:	6878                	flw	fa4,84(s0)
   125a4:	add6                	fsd	fs5,216(sp)
   125a6:	d8b74043          	fmadd.s	ft0,fa4,fa1,fs11,rmm
   125aa:	7516                	flw	fa0,100(sp)
   125ac:	70ff                	0x70ff
   125ae:	5c70                	lw	a2,124(s0)
   125b0:	2e1d                	jal	128e6 <impure_data+0x11e>
   125b2:	4ce5                	li	s9,25
   125b4:	f209e123          	0xf209e123
   125b8:	19c4                	addi	s1,sp,244
   125ba:	620afe43          	fmadd.d	ft8,fs5,ft0,fa2
   125be:	9774                	0x9774
   125c0:	7a58d047          	fmsub.d	ft0,fa7,ft5,fa5,unknown
   125c4:	524b09b7          	lui	s3,0x524b0
   125c8:	f044                	fsw	fs1,36(s0)
   125ca:	44a296cb          	0x44a296cb
   125ce:	2a90                	fld	fa2,16(a3)
   125d0:	95dc                	0x95dc
   125d2:	5149                	li	sp,-14
   125d4:	3ed6                	fld	ft9,368(sp)
   125d6:	e4b8                	fsw	fa4,72(s1)
   125d8:	e300                	fsw	fs0,0(a4)
   125da:	d4f8d21b          	0xd4f8d21b
   125de:	2966                	fld	fs2,88(sp)
   125e0:	19c4                	addi	s1,sp,244
   125e2:	d9ee                	sw	s11,240(sp)
   125e4:	88f6                	mv	a7,t4
   125e6:	74abb607          	fld	fa2,1866(s7) # fffe774a <__BSS_END__+0xfffd4b2e>
   125ea:	f8d0                	fsw	fa2,52(s1)
   125ec:	3295                	jal	11f50 <__errno+0xc24>
   125ee:	a7e1                	j	12db6 <__BSS_END__+0x19a>
   125f0:	8edc                	0x8edc
   125f2:	9371                	srli	a4,a4,0x3c
   125f4:	c096                	sw	t0,64(sp)
   125f6:	ba9f fbbc 0ad2      	0xad2fbbcba9f
   125fc:	9fe0c363          	blt	ra,t5,117e2 <__errno+0x4b6>
   12600:	10b4                	addi	a3,sp,104
   12602:	472a                	lw	a4,136(sp)
   12604:	da9c946b          	0xda9c946b
   12608:	37276997          	auipc	s3,0x37276
   1260c:	52fc                	lw	a5,100(a3)
   1260e:	04e4                	addi	s1,sp,588
   12610:	33b5                	jal	1237c <n+0x34>
   12612:	d192                	sw	tp,224(sp)
   12614:	ef0e                	fsw	ft3,156(sp)
   12616:	9ddda277          	0x9ddda277
   1261a:	4961                	li	s2,24
   1261c:	2d56                	fld	fs10,336(sp)
   1261e:	b582                	fsd	ft0,232(sp)
   12620:	6ca4d02f          	0x6ca4d02f
   12624:	7d0c0fc3          	0x7d0c0fc3
   12628:	96e2                	add	a3,a3,s8
   1262a:	a291                	j	1276e <sig+0x126>
   1262c:	b6988a4f          	fnmadd.q	fs4,fa7,fs1,fs6,rne
   12630:	7552                	flw	fa0,52(sp)
   12632:	3c24785b          	0x3c24785b
   12636:	eaee                	fsw	fs11,84(sp)
   12638:	3424                	fld	fs1,104(s0)
   1263a:	8799                	srai	a5,a5,0x6
   1263c:	fcb49693          	0xfcb49693
   12640:	4d84                	lw	s1,24(a1)
   12642:	21e6                	fld	ft3,88(sp)
   12644:	cea8                	sw	a0,88(a3)
   12646:	9e2d                	0x9e2d

00012648 <sig>:
   12648:	ceb7e983          	0xceb7e983
   1264c:	b200                	fsd	fs0,32(a2)
   1264e:	3989e693          	ori	a3,s3,920
   12652:	f915                	bnez	a0,12586 <rr+0xbe>
   12654:	9599                	srai	a1,a1,0x26
   12656:	cf89                	beqz	a5,12670 <sig+0x28>
   12658:	9fae                	add	t6,t6,a1
   1265a:	1ec0                	addi	s0,sp,884
   1265c:	f2f88007          	0xf2f88007
   12660:	eed5                	bnez	a3,1271c <sig+0xd4>
   12662:	2a24                	fld	fs1,80(a2)
   12664:	7c4e                	flw	fs8,240(sp)
   12666:	53b29c5b          	0x53b29c5b
   1266a:	21a1                	jal	12ab2 <impure_data+0x2ea>
   1266c:	83ae                	mv	t2,a1
   1266e:	af75                	j	12e2a <__BSS_END__+0x20e>
   12670:	d694                	sw	a3,40(a3)
   12672:	04fd                	addi	s1,s1,31
   12674:	7550094b          	0x7550094b
   12678:	9ac4                	0x9ac4
   1267a:	b2a6                	fsd	fs1,352(sp)
   1267c:	8022                	c.mv	zero,s0
   1267e:	e49d                	bnez	s1,126ac <sig+0x64>
   12680:	f162                	fsw	fs8,160(sp)
   12682:	7ed6                	flw	ft9,116(sp)
   12684:	14bb3a1b          	0x14bb3a1b
   12688:	d8dd                	beqz	s1,1263e <rr+0x176>
   1268a:	bb29                	j	123a4 <n+0x5c>
   1268c:	15c2                	slli	a1,a1,0x30
   1268e:	5c58                	lw	a4,60(s0)
   12690:	d848                	sw	a0,52(s0)
   12692:	7a80                	flw	fs0,48(a3)
   12694:	f449                	bnez	s0,1261e <rr+0x156>
   12696:	b122                	fsd	fs0,160(sp)
   12698:	a808                	fsd	fa0,16(s0)
   1269a:	59dc                	lw	a5,52(a1)
   1269c:	43e2                	lw	t2,24(sp)
   1269e:	bc14                	fsd	fa3,56(s0)
   126a0:	e304ff93          	andi	t6,s1,-464
   126a4:	cc97ee4b          	0xcc97ee4b
   126a8:	42ef6b57          	0x42ef6b57
   126ac:	839f 1436 0b45      	0xb451436839f
   126b2:	ae86                	fsd	ft1,344(sp)
   126b4:	6a843a17          	auipc	s4,0x6a843
   126b8:	fb91                	bnez	a5,125cc <rr+0x104>
   126ba:	2381                	jal	12bfa <d0inv+0x2>
   126bc:	0635                	addi	a2,a2,13
   126be:	09fd                	addi	s3,s3,31
   126c0:	a431aac3          	0xa431aac3
   126c4:	0269                	addi	tp,tp,26
   126c6:	d722                	sw	s0,172(sp)
   126c8:	df3e2697          	auipc	a3,0xdf3e2
   126cc:	915e                	add	sp,sp,s7
   126ce:	35e2                	fld	fa1,56(sp)
   126d0:	6956                	flw	fs2,84(sp)
   126d2:	edba                	fsw	fa4,216(sp)
   126d4:	7448                	flw	fa0,44(s0)
   126d6:	1d38                	addi	a4,sp,696
   126d8:	06df 9300 5f00      	0x5f00930006df
   126de:	961e                	add	a2,a2,t2
   126e0:	e960                	fsw	fs0,84(a0)
   126e2:	4addf2a7          	0x4addf2a7
   126e6:	884e                	mv	a6,s3
   126e8:	76b1                	lui	a3,0xfffec
   126ea:	7dfe                	flw	fs11,252(sp)
   126ec:	aa79                	j	1288a <impure_data+0xc2>
   126ee:	4079                	c.li	zero,30
   126f0:	378d                	jal	12652 <sig+0xa>
   126f2:	1f3a                	slli	t5,t5,0x2e
   126f4:	96c20697          	auipc	a3,0x96c20
   126f8:	268aea57          	0x268aea57
   126fc:	69a4                	flw	fs1,80(a1)
   126fe:	2c85                	jal	1296e <impure_data+0x1a6>
   12700:	f512                	fsw	ft4,168(sp)
   12702:	0474                	addi	a3,sp,524
   12704:	555c                	lw	a5,44(a0)
   12706:	2388                	fld	fa0,0(a5)
   12708:	58679953          	0x58679953
   1270c:	a3a0                	fsd	fs0,64(a5)
   1270e:	e73d                	bnez	a4,1277c <sig+0x134>
   12710:	1b9a                	slli	s7,s7,0x26
   12712:	04d34343          	0x4d34343
   12716:	699f e066 fc0b      	0xfc0be066699f
   1271c:	06f2                	slli	a3,a3,0x1c
   1271e:	cce6                	sw	s9,88(sp)
   12720:	dfa0                	sw	s0,120(a5)
   12722:	d94c                	sw	a1,52(a0)
   12724:	6c1ddca3          	0x6c1ddca3
   12728:	11f6                	slli	gp,gp,0x3d
   1272a:	e96c                	fsw	fa1,84(a0)
   1272c:	5db4                	lw	a3,120(a1)
   1272e:	4f69fc63          	bgeu	s3,s6,12c26 <__BSS_END__+0xa>
   12732:	c3e73bdb          	0xc3e73bdb
   12736:	a621                	j	12a3e <impure_data+0x276>
   12738:	2111                	jal	12b3c <impure_data+0x374>
   1273a:	9f29                	0x9f29
   1273c:	b86e1e6b          	0xb86e1e6b
   12740:	b74f923b          	0xb74f923b
   12744:	67a0                	flw	fs0,72(a5)
   12746:	5929                	li	s2,-22
   12748:	097f                	0x97f
   1274a:	c412                	sw	tp,8(sp)
   1274c:	8c1c8ca7          	0x8c1c8ca7
   12750:	cdb6                	sw	a3,216(sp)
   12752:	fe0f494f          	fnmadd.q	fs2,ft10,ft0,ft11,rmm
   12756:	87c5                	srai	a5,a5,0x11
   12758:	1aee                	slli	s5,s5,0x3b
   1275a:	50c0                	lw	s0,36(s1)
   1275c:	368e                	fld	fa3,224(sp)
   1275e:	8a26                	mv	s4,s1
   12760:	2232                	fld	ft4,264(sp)
   12762:	eaf1                	bnez	a3,12836 <impure_data+0x6e>
   12764:	e4d8                	fsw	fa4,12(s1)
   12766:	7dad                	lui	s11,0xfffeb
   12768:	2ac6                	fld	fs5,80(sp)
   1276a:	8aaa39eb          	0x8aaa39eb
   1276e:	08ca744f          	fnmadd.s	fs0,fs4,fa2,ft1
   12772:	f349                	bnez	a4,126f4 <sig+0xac>
   12774:	656c                	flw	fa1,76(a0)
   12776:	1e0c                	addi	a1,sp,816
   12778:	4e29                	li	t3,10
   1277a:	e96d                	bnez	a0,1286c <impure_data+0xa4>
   1277c:	d194                	sw	a3,32(a1)
   1277e:	8575                	srai	a0,a0,0x1d
   12780:	bd31                	j	1259c <rr+0xd4>
   12782:	e439                	bnez	s0,127d0 <impure_data+0x8>
   12784:	a74a77e3          	bgeu	s4,s4,121f2 <__errno+0xec6>
   12788:	5b88                	lw	a0,48(a5)
   1278a:	0f46                	slli	t5,t5,0x11
   1278c:	1152                	slli	sp,sp,0x34
   1278e:	f4e2                	fsw	fs8,104(sp)
   12790:	0ad8                	addi	a4,sp,340
   12792:	8040                	0x8040
   12794:	01ec                	addi	a1,sp,204
   12796:	e585                	bnez	a1,127be <sig+0x176>
   12798:	7536                	flw	fa0,108(sp)
   1279a:	a29d                	j	12900 <impure_data+0x138>
   1279c:	9326                	add	t1,t1,s1
   1279e:	55c1                	li	a1,-16
   127a0:	c63e                	sw	a5,12(sp)
   127a2:	5aee9ebb          	0x5aee9ebb
   127a6:	83d720c7          	fmsub.d	ft1,fa4,ft9,fa6,rdn
   127aa:	dba5ef67          	0xdba5ef67
   127ae:	59ff                	0x59ff
   127b0:	879b937b          	0x879b937b
   127b4:	c74c                	sw	a1,12(a4)
   127b6:	43a5                	li	t2,9
   127b8:	f825                	bnez	s0,12728 <sig+0xe0>
   127ba:	82b8                	0x82b8
   127bc:	4b3a                	lw	s6,140(sp)
   127be:	fdf0                	fsw	fa2,124(a1)
   127c0:	2fbe                	fld	ft11,456(sp)
   127c2:	8fc6                	mv	t6,a7
   127c4:	6da5                	lui	s11,0x9
   127c6:	114e                	slli	sp,sp,0x33

000127c8 <impure_data>:
   127c8:	0000                	unimp
   127ca:	0000                	unimp
   127cc:	2ab4                	fld	fa3,80(a3)
   127ce:	0001                	nop
   127d0:	2b1c                	fld	fa5,16(a4)
   127d2:	0001                	nop
   127d4:	2b84                	fld	fs1,16(a5)
   127d6:	0001                	nop
	...
   12870:	0001                	nop
   12872:	0000                	unimp
   12874:	0000                	unimp
   12876:	0000                	unimp
   12878:	330e                	fld	ft6,224(sp)
   1287a:	abcd                	j	12e6c <__BSS_END__+0x250>
   1287c:	1234                	addi	a3,sp,296
   1287e:	e66d                	bnez	a2,12968 <impure_data+0x1a0>
   12880:	deec                	sw	a1,124(a3)
   12882:	0005                	c.nop	1
   12884:	0000000b          	0xb
	...

Disassembly of section .sdata:

00012bf0 <_global_impure_ptr>:
   12bf0:	27c8                	fld	fa0,136(a5)
   12bf2:	0001                	nop

00012bf4 <__dso_handle>:
   12bf4:	0000                	unimp
	...

00012bf8 <d0inv>:
   12bf8:	71df f09b       	0x27c8f09b71df

00012bfc <_impure_ptr>:
   12bfc:	27c8                	fld	fa0,136(a5)
   12bfe:	0001                	nop

Disassembly of section .bss:

00012c00 <completed.1>:
   12c00:	0000                	unimp
	...

00012c04 <object.0>:
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
  1c:	326d                	jal	fffff9c6 <__BSS_END__+0xfffecdaa>
  1e:	3070                	fld	fa2,224(s0)
	...
