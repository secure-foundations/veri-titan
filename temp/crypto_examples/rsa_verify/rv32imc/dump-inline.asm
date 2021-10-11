
rsa_rv.elf:     file format elf32-littleriscv


Disassembly of section .text:

00010074 <main>:
   10074:	b7010113          	addi	sp,sp,-1168
   10078:	48912223          	sw	s1,1156(sp)
   1007c:	66c5                	lui	a3,0x11
   1007e:	0b01a483          	lw	s1,176(gp) # 11e58 <d0inv>
   10082:	5a868693          	addi	a3,a3,1448 # 115a8 <n>
   10086:	49212023          	sw	s2,1152(sp)
   1008a:	30068913          	addi	s2,a3,768
   1008e:	864a                	mv	a2,s2
   10090:	18068693          	addi	a3,a3,384
   10094:	030c                	addi	a1,sp,384
   10096:	8526                	mv	a0,s1
   10098:	48812423          	sw	s0,1160(sp)
   1009c:	48112623          	sw	ra,1164(sp)
   100a0:	4421                	li	s0,8
   100a2:	20f9                	jal	10170 <mont_mul.constprop.0>
   100a4:	0314                	addi	a3,sp,384
   100a6:	8636                	mv	a2,a3
   100a8:	060c                	addi	a1,sp,768
   100aa:	8526                	mv	a0,s1
   100ac:	20d1                	jal	10170 <mont_mul.constprop.0>
   100ae:	0614                	addi	a3,sp,768
   100b0:	147d                	addi	s0,s0,-1
   100b2:	8636                	mv	a2,a3
   100b4:	030c                	addi	a1,sp,384
   100b6:	8526                	mv	a0,s1
   100b8:	2865                	jal	10170 <mont_mul.constprop.0>
   100ba:	f46d                	bnez	s0,100a4 <main+0x30>
   100bc:	8526                	mv	a0,s1
   100be:	86ca                	mv	a3,s2
   100c0:	0310                	addi	a2,sp,384
   100c2:	858a                	mv	a1,sp
   100c4:	2075                	jal	10170 <mont_mul.constprop.0>
   100c6:	48c12083          	lw	ra,1164(sp)
   100ca:	48812403          	lw	s0,1160(sp)
   100ce:	48412483          	lw	s1,1156(sp)
   100d2:	48012903          	lw	s2,1152(sp)
   100d6:	4501                	li	a0,0
   100d8:	49010113          	addi	sp,sp,1168
   100dc:	8082                	ret

000100de <register_fini>:
   100de:	00000793          	li	a5,0
   100e2:	c789                	beqz	a5,100ec <register_fini+0xe>
   100e4:	6541                	lui	a0,0x10
   100e6:	4cc50513          	addi	a0,a0,1228 # 104cc <__libc_fini_array>
   100ea:	aee1                	j	104c2 <atexit>
   100ec:	8082                	ret

000100ee <_start>:
   100ee:	00002197          	auipc	gp,0x2
   100f2:	cba18193          	addi	gp,gp,-838 # 11da8 <__global_pointer$>
   100f6:	0b818513          	addi	a0,gp,184 # 11e60 <_edata>
   100fa:	0d418613          	addi	a2,gp,212 # 11e7c <__BSS_END__>
   100fe:	8e09                	sub	a2,a2,a0
   10100:	4581                	li	a1,0
   10102:	2ca9                	jal	1035c <memset>
   10104:	00000517          	auipc	a0,0x0
   10108:	3be50513          	addi	a0,a0,958 # 104c2 <atexit>
   1010c:	c511                	beqz	a0,10118 <_start+0x2a>
   1010e:	00000517          	auipc	a0,0x0
   10112:	3be50513          	addi	a0,a0,958 # 104cc <__libc_fini_array>
   10116:	2675                	jal	104c2 <atexit>
   10118:	2ae9                	jal	102f2 <__libc_init_array>
   1011a:	4502                	lw	a0,0(sp)
   1011c:	004c                	addi	a1,sp,4
   1011e:	4601                	li	a2,0
   10120:	3f91                	jal	10074 <main>
   10122:	aa5d                	j	102d8 <exit>

00010124 <__do_global_dtors_aux>:
   10124:	0b81c703          	lbu	a4,184(gp) # 11e60 <_edata>
   10128:	e715                	bnez	a4,10154 <__do_global_dtors_aux+0x30>
   1012a:	1141                	addi	sp,sp,-16
   1012c:	c422                	sw	s0,8(sp)
   1012e:	843e                	mv	s0,a5
   10130:	c606                	sw	ra,12(sp)
   10132:	00000793          	li	a5,0
   10136:	cb81                	beqz	a5,10146 <__do_global_dtors_aux+0x22>
   10138:	6545                	lui	a0,0x11
   1013a:	59450513          	addi	a0,a0,1428 # 11594 <__FRAME_END__>
   1013e:	00000097          	auipc	ra,0x0
   10142:	000000e7          	jalr	zero # 0 <main-0x10074>
   10146:	4785                	li	a5,1
   10148:	40b2                	lw	ra,12(sp)
   1014a:	0af18c23          	sb	a5,184(gp) # 11e60 <_edata>
   1014e:	4422                	lw	s0,8(sp)
   10150:	0141                	addi	sp,sp,16
   10152:	8082                	ret
   10154:	8082                	ret

00010156 <frame_dummy>:
   10156:	00000793          	li	a5,0
   1015a:	cb91                	beqz	a5,1016e <frame_dummy+0x18>
   1015c:	6545                	lui	a0,0x11
   1015e:	0bc18593          	addi	a1,gp,188 # 11e64 <object.0>
   10162:	59450513          	addi	a0,a0,1428 # 11594 <__FRAME_END__>
   10166:	00000317          	auipc	t1,0x0
   1016a:	00000067          	jr	zero # 0 <main-0x10074>
   1016e:	8082                	ret

00010170 <mont_mul.constprop.0>:
   10170:	7179                	addi	sp,sp,-48
   10172:	83ae                	mv	t2,a1
   10174:	d422                	sw	s0,40(sp)
   10176:	cc52                	sw	s4,24(sp)
   10178:	8432                	mv	s0,a2
   1017a:	8a2a                	mv	s4,a0
   1017c:	18000613          	li	a2,384
   10180:	851e                	mv	a0,t2
   10182:	4581                	li	a1,0
   10184:	d226                	sw	s1,36(sp)
   10186:	d04a                	sw	s2,32(sp)
   10188:	ce4e                	sw	s3,28(sp)
   1018a:	ca56                	sw	s5,20(sp)
   1018c:	c85a                	sw	s6,16(sp)
   1018e:	c65e                	sw	s7,12(sp)
   10190:	84b6                	mv	s1,a3
   10192:	d606                	sw	ra,44(sp)
   10194:	c462                	sw	s8,8(sp)
   10196:	c266                	sw	s9,4(sp)
   10198:	22d1                	jal	1035c <memset>
   1019a:	6945                	lui	s2,0x11
   1019c:	69c5                	lui	s3,0x11
   1019e:	82a2                	mv	t0,s0
   101a0:	18040b93          	addi	s7,s0,384
   101a4:	83aa                	mv	t2,a0
   101a6:	5a890413          	addi	s0,s2,1448 # 115a8 <n>
   101aa:	00448b13          	addi	s6,s1,4
   101ae:	5ac98993          	addi	s3,s3,1452 # 115ac <n+0x4>
   101b2:	98018f93          	addi	t6,gp,-1664 # 11728 <rr>
   101b6:	5a890a93          	addi	s5,s2,1448
   101ba:	0002ae03          	lw	t3,0(t0)
   101be:	4090                	lw	a2,0(s1)
   101c0:	0003a783          	lw	a5,0(t2)
   101c4:	4018                	lw	a4,0(s0)
   101c6:	02ce06b3          	mul	a3,t3,a2
   101ca:	88da                	mv	a7,s6
   101cc:	8f1e                	mv	t5,t2
   101ce:	884e                	mv	a6,s3
   101d0:	8456                	mv	s0,s5
   101d2:	5a890e93          	addi	t4,s2,1448
   101d6:	851e                	mv	a0,t2
   101d8:	97b6                	add	a5,a5,a3
   101da:	02fa0333          	mul	t1,s4,a5
   101de:	00d7b6b3          	sltu	a3,a5,a3
   101e2:	02e305b3          	mul	a1,t1,a4
   101e6:	02ce3633          	mulhu	a2,t3,a2
   101ea:	97ae                	add	a5,a5,a1
   101ec:	00b7b7b3          	sltu	a5,a5,a1
   101f0:	02e33733          	mulhu	a4,t1,a4
   101f4:	96b2                	add	a3,a3,a2
   101f6:	97ba                	add	a5,a5,a4
   101f8:	0008ac03          	lw	s8,0(a7)
   101fc:	00082583          	lw	a1,0(a6)
   10200:	4150                	lw	a2,4(a0)
   10202:	038e0733          	mul	a4,t3,s8
   10206:	0511                	addi	a0,a0,4
   10208:	9636                	add	a2,a2,a3
   1020a:	00d636b3          	sltu	a3,a2,a3
   1020e:	0811                	addi	a6,a6,4
   10210:	0891                	addi	a7,a7,4
   10212:	02b30cb3          	mul	s9,t1,a1
   10216:	9732                	add	a4,a4,a2
   10218:	00c73633          	sltu	a2,a4,a2
   1021c:	038e3c33          	mulhu	s8,t3,s8
   10220:	97e6                	add	a5,a5,s9
   10222:	973e                	add	a4,a4,a5
   10224:	0197bcb3          	sltu	s9,a5,s9
   10228:	fee52e23          	sw	a4,-4(a0)
   1022c:	00f737b3          	sltu	a5,a4,a5
   10230:	02b335b3          	mulhu	a1,t1,a1
   10234:	96e2                	add	a3,a3,s8
   10236:	96b2                	add	a3,a3,a2
   10238:	95e6                	add	a1,a1,s9
   1023a:	97ae                	add	a5,a5,a1
   1023c:	fb0f9ee3          	bne	t6,a6,101f8 <mont_mul.constprop.0+0x88>
   10240:	97b6                	add	a5,a5,a3
   10242:	16f3ae23          	sw	a5,380(t2)
   10246:	02d7e263          	bltu	a5,a3,1026a <mont_mul.constprop.0+0xfa>
   1024a:	0291                	addi	t0,t0,4
   1024c:	f65b97e3          	bne	s7,t0,101ba <mont_mul.constprop.0+0x4a>
   10250:	50b2                	lw	ra,44(sp)
   10252:	5422                	lw	s0,40(sp)
   10254:	5492                	lw	s1,36(sp)
   10256:	5902                	lw	s2,32(sp)
   10258:	49f2                	lw	s3,28(sp)
   1025a:	4a62                	lw	s4,24(sp)
   1025c:	4ad2                	lw	s5,20(sp)
   1025e:	4b42                	lw	s6,16(sp)
   10260:	4bb2                	lw	s7,12(sp)
   10262:	4c22                	lw	s8,8(sp)
   10264:	4c92                	lw	s9,4(sp)
   10266:	6145                	addi	sp,sp,48
   10268:	8082                	ret
   1026a:	4781                	li	a5,0
   1026c:	4601                	li	a2,0
   1026e:	000f2703          	lw	a4,0(t5)
   10272:	000ea683          	lw	a3,0(t4)
   10276:	0e91                	addi	t4,t4,4
   10278:	97ba                	add	a5,a5,a4
   1027a:	40d786b3          	sub	a3,a5,a3
   1027e:	00e7b733          	sltu	a4,a5,a4
   10282:	9732                	add	a4,a4,a2
   10284:	00d7b7b3          	sltu	a5,a5,a3
   10288:	00df2023          	sw	a3,0(t5)
   1028c:	40f707b3          	sub	a5,a4,a5
   10290:	41f7d613          	srai	a2,a5,0x1f
   10294:	0f11                	addi	t5,t5,4
   10296:	fdfe9ce3          	bne	t4,t6,1026e <mont_mul.constprop.0+0xfe>
   1029a:	bf45                	j	1024a <mont_mul.constprop.0+0xda>

0001029c <mul32>:
   1029c:	87ae                	mv	a5,a1
   1029e:	02b535b3          	mulhu	a1,a0,a1
   102a2:	02f50533          	mul	a0,a0,a5
   102a6:	8082                	ret

000102a8 <mula32>:
   102a8:	02b507b3          	mul	a5,a0,a1
   102ac:	02b535b3          	mulhu	a1,a0,a1
   102b0:	00c78533          	add	a0,a5,a2
   102b4:	00f537b3          	sltu	a5,a0,a5
   102b8:	95be                	add	a1,a1,a5
   102ba:	8082                	ret

000102bc <mulaa32>:
   102bc:	02b50733          	mul	a4,a0,a1
   102c0:	96b2                	add	a3,a3,a2
   102c2:	00c6b633          	sltu	a2,a3,a2
   102c6:	02b537b3          	mulhu	a5,a0,a1
   102ca:	00d70533          	add	a0,a4,a3
   102ce:	00e535b3          	sltu	a1,a0,a4
   102d2:	97b2                	add	a5,a5,a2
   102d4:	95be                	add	a1,a1,a5
   102d6:	8082                	ret

000102d8 <exit>:
   102d8:	1141                	addi	sp,sp,-16
   102da:	4581                	li	a1,0
   102dc:	c422                	sw	s0,8(sp)
   102de:	c606                	sw	ra,12(sp)
   102e0:	842a                	mv	s0,a0
   102e2:	220d                	jal	10404 <__call_exitprocs>
   102e4:	0a81a503          	lw	a0,168(gp) # 11e50 <_global_impure_ptr>
   102e8:	5d5c                	lw	a5,60(a0)
   102ea:	c391                	beqz	a5,102ee <exit+0x16>
   102ec:	9782                	jalr	a5
   102ee:	8522                	mv	a0,s0
   102f0:	2cb5                	jal	1056c <_exit>

000102f2 <__libc_init_array>:
   102f2:	1141                	addi	sp,sp,-16
   102f4:	c422                	sw	s0,8(sp)
   102f6:	c04a                	sw	s2,0(sp)
   102f8:	6445                	lui	s0,0x11
   102fa:	6945                	lui	s2,0x11
   102fc:	59840793          	addi	a5,s0,1432 # 11598 <__init_array_start>
   10300:	59890913          	addi	s2,s2,1432 # 11598 <__init_array_start>
   10304:	40f90933          	sub	s2,s2,a5
   10308:	c606                	sw	ra,12(sp)
   1030a:	c226                	sw	s1,4(sp)
   1030c:	40295913          	srai	s2,s2,0x2
   10310:	00090b63          	beqz	s2,10326 <__libc_init_array+0x34>
   10314:	59840413          	addi	s0,s0,1432
   10318:	4481                	li	s1,0
   1031a:	401c                	lw	a5,0(s0)
   1031c:	0485                	addi	s1,s1,1
   1031e:	0411                	addi	s0,s0,4
   10320:	9782                	jalr	a5
   10322:	fe991ce3          	bne	s2,s1,1031a <__libc_init_array+0x28>
   10326:	6445                	lui	s0,0x11
   10328:	6945                	lui	s2,0x11
   1032a:	59840793          	addi	a5,s0,1432 # 11598 <__init_array_start>
   1032e:	5a090913          	addi	s2,s2,1440 # 115a0 <__init_array_end>
   10332:	40f90933          	sub	s2,s2,a5
   10336:	40295913          	srai	s2,s2,0x2
   1033a:	00090b63          	beqz	s2,10350 <__libc_init_array+0x5e>
   1033e:	59840413          	addi	s0,s0,1432
   10342:	4481                	li	s1,0
   10344:	401c                	lw	a5,0(s0)
   10346:	0485                	addi	s1,s1,1
   10348:	0411                	addi	s0,s0,4
   1034a:	9782                	jalr	a5
   1034c:	fe991ce3          	bne	s2,s1,10344 <__libc_init_array+0x52>
   10350:	40b2                	lw	ra,12(sp)
   10352:	4422                	lw	s0,8(sp)
   10354:	4492                	lw	s1,4(sp)
   10356:	4902                	lw	s2,0(sp)
   10358:	0141                	addi	sp,sp,16
   1035a:	8082                	ret

0001035c <memset>:
   1035c:	433d                	li	t1,15
   1035e:	872a                	mv	a4,a0
   10360:	02c37363          	bgeu	t1,a2,10386 <memset+0x2a>
   10364:	00f77793          	andi	a5,a4,15
   10368:	efbd                	bnez	a5,103e6 <memset+0x8a>
   1036a:	e5ad                	bnez	a1,103d4 <memset+0x78>
   1036c:	ff067693          	andi	a3,a2,-16
   10370:	8a3d                	andi	a2,a2,15
   10372:	96ba                	add	a3,a3,a4
   10374:	c30c                	sw	a1,0(a4)
   10376:	c34c                	sw	a1,4(a4)
   10378:	c70c                	sw	a1,8(a4)
   1037a:	c74c                	sw	a1,12(a4)
   1037c:	0741                	addi	a4,a4,16
   1037e:	fed76be3          	bltu	a4,a3,10374 <memset+0x18>
   10382:	e211                	bnez	a2,10386 <memset+0x2a>
   10384:	8082                	ret
   10386:	40c306b3          	sub	a3,t1,a2
   1038a:	068a                	slli	a3,a3,0x2
   1038c:	00000297          	auipc	t0,0x0
   10390:	9696                	add	a3,a3,t0
   10392:	00a68067          	jr	10(a3)
   10396:	00b70723          	sb	a1,14(a4)
   1039a:	00b706a3          	sb	a1,13(a4)
   1039e:	00b70623          	sb	a1,12(a4)
   103a2:	00b705a3          	sb	a1,11(a4)
   103a6:	00b70523          	sb	a1,10(a4)
   103aa:	00b704a3          	sb	a1,9(a4)
   103ae:	00b70423          	sb	a1,8(a4)
   103b2:	00b703a3          	sb	a1,7(a4)
   103b6:	00b70323          	sb	a1,6(a4)
   103ba:	00b702a3          	sb	a1,5(a4)
   103be:	00b70223          	sb	a1,4(a4)
   103c2:	00b701a3          	sb	a1,3(a4)
   103c6:	00b70123          	sb	a1,2(a4)
   103ca:	00b700a3          	sb	a1,1(a4)
   103ce:	00b70023          	sb	a1,0(a4)
   103d2:	8082                	ret
   103d4:	0ff5f593          	andi	a1,a1,255
   103d8:	00859693          	slli	a3,a1,0x8
   103dc:	8dd5                	or	a1,a1,a3
   103de:	01059693          	slli	a3,a1,0x10
   103e2:	8dd5                	or	a1,a1,a3
   103e4:	b761                	j	1036c <memset+0x10>
   103e6:	00279693          	slli	a3,a5,0x2
   103ea:	00000297          	auipc	t0,0x0
   103ee:	9696                	add	a3,a3,t0
   103f0:	8286                	mv	t0,ra
   103f2:	fa8680e7          	jalr	-88(a3)
   103f6:	8096                	mv	ra,t0
   103f8:	17c1                	addi	a5,a5,-16
   103fa:	8f1d                	sub	a4,a4,a5
   103fc:	963e                	add	a2,a2,a5
   103fe:	f8c374e3          	bgeu	t1,a2,10386 <memset+0x2a>
   10402:	b7a5                	j	1036a <memset+0xe>

00010404 <__call_exitprocs>:
   10404:	7179                	addi	sp,sp,-48
   10406:	cc52                	sw	s4,24(sp)
   10408:	0a81aa03          	lw	s4,168(gp) # 11e50 <_global_impure_ptr>
   1040c:	d04a                	sw	s2,32(sp)
   1040e:	d606                	sw	ra,44(sp)
   10410:	148a2903          	lw	s2,328(s4)
   10414:	d422                	sw	s0,40(sp)
   10416:	d226                	sw	s1,36(sp)
   10418:	ce4e                	sw	s3,28(sp)
   1041a:	ca56                	sw	s5,20(sp)
   1041c:	c85a                	sw	s6,16(sp)
   1041e:	c65e                	sw	s7,12(sp)
   10420:	c462                	sw	s8,8(sp)
   10422:	02090863          	beqz	s2,10452 <__call_exitprocs+0x4e>
   10426:	8b2a                	mv	s6,a0
   10428:	8bae                	mv	s7,a1
   1042a:	4a85                	li	s5,1
   1042c:	59fd                	li	s3,-1
   1042e:	00492483          	lw	s1,4(s2)
   10432:	fff48413          	addi	s0,s1,-1
   10436:	00044e63          	bltz	s0,10452 <__call_exitprocs+0x4e>
   1043a:	048a                	slli	s1,s1,0x2
   1043c:	94ca                	add	s1,s1,s2
   1043e:	020b8663          	beqz	s7,1046a <__call_exitprocs+0x66>
   10442:	1044a783          	lw	a5,260(s1)
   10446:	03778263          	beq	a5,s7,1046a <__call_exitprocs+0x66>
   1044a:	147d                	addi	s0,s0,-1
   1044c:	14f1                	addi	s1,s1,-4
   1044e:	ff3418e3          	bne	s0,s3,1043e <__call_exitprocs+0x3a>
   10452:	50b2                	lw	ra,44(sp)
   10454:	5422                	lw	s0,40(sp)
   10456:	5492                	lw	s1,36(sp)
   10458:	5902                	lw	s2,32(sp)
   1045a:	49f2                	lw	s3,28(sp)
   1045c:	4a62                	lw	s4,24(sp)
   1045e:	4ad2                	lw	s5,20(sp)
   10460:	4b42                	lw	s6,16(sp)
   10462:	4bb2                	lw	s7,12(sp)
   10464:	4c22                	lw	s8,8(sp)
   10466:	6145                	addi	sp,sp,48
   10468:	8082                	ret
   1046a:	00492783          	lw	a5,4(s2)
   1046e:	40d4                	lw	a3,4(s1)
   10470:	17fd                	addi	a5,a5,-1
   10472:	04878263          	beq	a5,s0,104b6 <__call_exitprocs+0xb2>
   10476:	0004a223          	sw	zero,4(s1)
   1047a:	dae1                	beqz	a3,1044a <__call_exitprocs+0x46>
   1047c:	18892783          	lw	a5,392(s2)
   10480:	008a9733          	sll	a4,s5,s0
   10484:	00492c03          	lw	s8,4(s2)
   10488:	8ff9                	and	a5,a5,a4
   1048a:	ef89                	bnez	a5,104a4 <__call_exitprocs+0xa0>
   1048c:	9682                	jalr	a3
   1048e:	00492703          	lw	a4,4(s2)
   10492:	148a2783          	lw	a5,328(s4)
   10496:	01871463          	bne	a4,s8,1049e <__call_exitprocs+0x9a>
   1049a:	fb2788e3          	beq	a5,s2,1044a <__call_exitprocs+0x46>
   1049e:	dbd5                	beqz	a5,10452 <__call_exitprocs+0x4e>
   104a0:	893e                	mv	s2,a5
   104a2:	b771                	j	1042e <__call_exitprocs+0x2a>
   104a4:	18c92783          	lw	a5,396(s2)
   104a8:	0844a583          	lw	a1,132(s1)
   104ac:	8f7d                	and	a4,a4,a5
   104ae:	e719                	bnez	a4,104bc <__call_exitprocs+0xb8>
   104b0:	855a                	mv	a0,s6
   104b2:	9682                	jalr	a3
   104b4:	bfe9                	j	1048e <__call_exitprocs+0x8a>
   104b6:	00892223          	sw	s0,4(s2)
   104ba:	b7c1                	j	1047a <__call_exitprocs+0x76>
   104bc:	852e                	mv	a0,a1
   104be:	9682                	jalr	a3
   104c0:	b7f9                	j	1048e <__call_exitprocs+0x8a>

000104c2 <atexit>:
   104c2:	85aa                	mv	a1,a0
   104c4:	4681                	li	a3,0
   104c6:	4601                	li	a2,0
   104c8:	4501                	li	a0,0
   104ca:	a81d                	j	10500 <__register_exitproc>

000104cc <__libc_fini_array>:
   104cc:	1141                	addi	sp,sp,-16
   104ce:	c422                	sw	s0,8(sp)
   104d0:	67c5                	lui	a5,0x11
   104d2:	6445                	lui	s0,0x11
   104d4:	5a040413          	addi	s0,s0,1440 # 115a0 <__init_array_end>
   104d8:	5a478793          	addi	a5,a5,1444 # 115a4 <__fini_array_end>
   104dc:	8f81                	sub	a5,a5,s0
   104de:	c226                	sw	s1,4(sp)
   104e0:	c606                	sw	ra,12(sp)
   104e2:	4027d493          	srai	s1,a5,0x2
   104e6:	c881                	beqz	s1,104f6 <__libc_fini_array+0x2a>
   104e8:	17f1                	addi	a5,a5,-4
   104ea:	943e                	add	s0,s0,a5
   104ec:	401c                	lw	a5,0(s0)
   104ee:	14fd                	addi	s1,s1,-1
   104f0:	1471                	addi	s0,s0,-4
   104f2:	9782                	jalr	a5
   104f4:	fce5                	bnez	s1,104ec <__libc_fini_array+0x20>
   104f6:	40b2                	lw	ra,12(sp)
   104f8:	4422                	lw	s0,8(sp)
   104fa:	4492                	lw	s1,4(sp)
   104fc:	0141                	addi	sp,sp,16
   104fe:	8082                	ret

00010500 <__register_exitproc>:
   10500:	0a81a703          	lw	a4,168(gp) # 11e50 <_global_impure_ptr>
   10504:	14872783          	lw	a5,328(a4)
   10508:	c3a1                	beqz	a5,10548 <__register_exitproc+0x48>
   1050a:	43d8                	lw	a4,4(a5)
   1050c:	487d                	li	a6,31
   1050e:	04e84d63          	blt	a6,a4,10568 <__register_exitproc+0x68>
   10512:	00271813          	slli	a6,a4,0x2
   10516:	c11d                	beqz	a0,1053c <__register_exitproc+0x3c>
   10518:	01078333          	add	t1,a5,a6
   1051c:	08c32423          	sw	a2,136(t1) # 101ee <mont_mul.constprop.0+0x7e>
   10520:	1887a883          	lw	a7,392(a5)
   10524:	4605                	li	a2,1
   10526:	00e61633          	sll	a2,a2,a4
   1052a:	00c8e8b3          	or	a7,a7,a2
   1052e:	1917a423          	sw	a7,392(a5)
   10532:	10d32423          	sw	a3,264(t1)
   10536:	4689                	li	a3,2
   10538:	00d50d63          	beq	a0,a3,10552 <__register_exitproc+0x52>
   1053c:	0705                	addi	a4,a4,1
   1053e:	c3d8                	sw	a4,4(a5)
   10540:	97c2                	add	a5,a5,a6
   10542:	c78c                	sw	a1,8(a5)
   10544:	4501                	li	a0,0
   10546:	8082                	ret
   10548:	14c70793          	addi	a5,a4,332
   1054c:	14f72423          	sw	a5,328(a4)
   10550:	bf6d                	j	1050a <__register_exitproc+0xa>
   10552:	18c7a683          	lw	a3,396(a5)
   10556:	0705                	addi	a4,a4,1
   10558:	c3d8                	sw	a4,4(a5)
   1055a:	8e55                	or	a2,a2,a3
   1055c:	18c7a623          	sw	a2,396(a5)
   10560:	97c2                	add	a5,a5,a6
   10562:	c78c                	sw	a1,8(a5)
   10564:	4501                	li	a0,0
   10566:	8082                	ret
   10568:	557d                	li	a0,-1
   1056a:	8082                	ret

0001056c <_exit>:
   1056c:	05d00893          	li	a7,93
   10570:	00000073          	ecall
   10574:	00054363          	bltz	a0,1057a <_exit+0xe>
   10578:	a001                	j	10578 <_exit+0xc>
   1057a:	1141                	addi	sp,sp,-16
   1057c:	c422                	sw	s0,8(sp)
   1057e:	842a                	mv	s0,a0
   10580:	c606                	sw	ra,12(sp)
   10582:	40800433          	neg	s0,s0
   10586:	2019                	jal	1058c <__errno>
   10588:	c100                	sw	s0,0(a0)
   1058a:	a001                	j	1058a <_exit+0x1e>

0001058c <__errno>:
   1058c:	0b41a503          	lw	a0,180(gp) # 11e5c <_impure_ptr>
   10590:	8082                	ret

Disassembly of section .eh_frame:

00011594 <__FRAME_END__>:
   11594:	0000                	unimp
	...

Disassembly of section .init_array:

00011598 <__init_array_start>:
   11598:	00de                	slli	ra,ra,0x17
   1159a:	0001                	nop

0001159c <__frame_dummy_init_array_entry>:
   1159c:	0156                	slli	sp,sp,0x15
   1159e:	0001                	nop

Disassembly of section .fini_array:

000115a0 <__do_global_dtors_aux_fini_array_entry>:
   115a0:	0124                	addi	s1,sp,136
   115a2:	0001                	nop

Disassembly of section .data:

000115a8 <n>:
   115a8:	75e1                	lui	a1,0xffff8
   115aa:	6a6a                	flw	fs4,152(sp)
   115ac:	ddc5                	beqz	a1,11564 <__errno+0xfd8>
   115ae:	a018                	fsd	fa4,0(s0)
   115b0:	b168                	fsd	fa0,224(a0)
   115b2:	05a5687b          	0x5a5687b
   115b6:	8e82                	jr	t4
   115b8:	7dbfffa7          	0x7dbfffa7
   115bc:	2ac5                	jal	117ac <rr+0x84>
   115be:	c872                	sw	t3,16(sp)
   115c0:	f84d21cf          	fnmadd.s	ft3,fs10,ft4,ft11,rdn
   115c4:	2531                	jal	11bd0 <impure_data+0x1a8>
   115c6:	e131                	bnez	a0,1160a <n+0x62>
   115c8:	0ce3f8a3          	0xce3f8a3
   115cc:	f988                	fsw	fa0,48(a1)
   115ce:	a825                	j	11606 <n+0x5e>
   115d0:	1964                	addi	s1,sp,188
   115d2:	57f5                	li	a5,-3
   115d4:	206a                	fld	ft0,152(sp)
   115d6:	b27e                	fsd	ft11,288(sp)
   115d8:	d008                	sw	a0,32(s0)
   115da:	8e1d                	sub	a2,a2,a5
   115dc:	1c4fb8d7          	0x1c4fb8d7
   115e0:	b142                	fsd	fa6,160(sp)
   115e2:	e7b3824f          	fnmadd.q	ft4,ft7,fs11,ft8,rne
   115e6:	63661c8b          	0x63661c8b
   115ea:	7b9d                	lui	s7,0xfffe7
   115ec:	d0f2                	sw	t3,96(sp)
   115ee:	c56a                	sw	s10,136(sp)
   115f0:	ef762d5b          	0xef762d5b
   115f4:	4b1431e3          	0x4b1431e3
   115f8:	8eb9                	xor	a3,a3,a4
   115fa:	8ae2                	mv	s5,s8
   115fc:	b7aa                	fsd	fa0,488(sp)
   115fe:	d41d                	beqz	s0,1152c <__errno+0xfa0>
   11600:	43cccdf7          	0x43cccdf7
   11604:	4a84                	lw	s1,16(a3)
   11606:	385091b7          	lui	gp,0x38509
   1160a:	8018                	0x8018
   1160c:	4d0d                	li	s10,3
   1160e:	d01530e7          	0xd01530e7
   11612:	b62e                	fsd	fa1,296(sp)
   11614:	74d2                	flw	fs1,52(sp)
   11616:	2355                	jal	11bba <impure_data+0x192>
   11618:	f251                	bnez	a2,1159c <__frame_dummy_init_array_entry>
   1161a:	8c28                	0x8c28
   1161c:	def2                	sw	t3,124(sp)
   1161e:	4f40                	lw	s0,28(a4)
   11620:	24e2efdb          	0x24e2efdb
   11624:	1ff2                	slli	t6,t6,0x3c
   11626:	9ebd                	0x9ebd
   11628:	49ee                	lw	s3,216(sp)
   1162a:	a938fa7b          	0xa938fa7b
   1162e:	2819                	jal	11644 <n+0x9c>
   11630:	b8c8                	fsd	fa0,176(s1)
   11632:	6e66                	flw	ft8,88(sp)
   11634:	1546                	slli	a0,a0,0x31
   11636:	24e4                	fld	fs1,200(s1)
   11638:	3a7c                	fld	fa5,240(a2)
   1163a:	4d78                	lw	a4,92(a0)
   1163c:	7d3d                	lui	s10,0xfffef
   1163e:	d294                	sw	a3,32(a3)
   11640:	69e9                	lui	s3,0x1a
   11642:	1ab2                	slli	s5,s5,0x2c
   11644:	9f16                	add	t5,t5,t0
   11646:	8f7bfad3          	0x8f7bfad3
   1164a:	b510aab7          	lui	s5,0xb510a
   1164e:	49d8                	lw	a4,20(a1)
   11650:	35bf0dfb          	0x35bf0dfb
   11654:	4754                	lw	a3,12(a4)
   11656:	ccc9eb27          	0xccc9eb27
   1165a:	069e                	slli	a3,a3,0x7
   1165c:	437e                	lw	t1,220(sp)
   1165e:	c13c                	sw	a5,64(a0)
   11660:	0f60                	addi	s0,sp,924
   11662:	e3bc                	fsw	fa5,64(a5)
   11664:	c9e0e12f          	0xc9e0e12f
   11668:	c253ac43          	fmadd.d	fs8,ft7,ft5,fs8,rdn
   1166c:	40e0                	lw	s0,68(s1)
   1166e:	89c2                	mv	s3,a6
   11670:	a4e5                	j	11958 <sig+0xb0>
   11672:	4bc0c4ab          	0x4bc0c4ab
   11676:	c462edf3          	csrrsi	s11,0xc46,5
   1167a:	5402                	lw	s0,32(sp)
   1167c:	b0bd                	j	10eea <__errno+0x95e>
   1167e:	4021                	c.li	zero,8
   11680:	6241                	lui	tp,0x10
   11682:	945f996b          	0x945f996b
   11686:	c3d9                	beqz	a5,1170c <n+0x164>
   11688:	ac60                	fsd	fs0,216(s0)
   1168a:	0bf5a137          	lui	sp,0xbf5a
   1168e:	f025                	bnez	s0,115ee <n+0x46>
   11690:	c8c7100f          	0xc8c7100f
   11694:	6b88                	flw	fa0,16(a5)
   11696:	b70d                	j	115b8 <n+0x10>
   11698:	6a8c                	flw	fa1,16(a3)
   1169a:	7891                	lui	a7,0xfffe4
   1169c:	0e5d                	addi	t3,t3,23
   1169e:	dcb93337          	lui	t1,0xdcb93
   116a2:	3970                	fld	fa2,240(a0)
   116a4:	58b4                	lw	a3,112(s1)
   116a6:	af4c                	fsd	fa1,152(a4)
   116a8:	cb0d                	beqz	a4,116da <n+0x132>
   116aa:	5f78                	lw	a4,124(a4)
   116ac:	b02d90b7          	lui	ra,0xb02d9
   116b0:	3d05                	jal	114e0 <__errno+0xf54>
   116b2:	eb6c                	fsw	fa1,84(a4)
   116b4:	c71a                	sw	t1,140(sp)
   116b6:	5f0f04af          	0x5f0f04af
   116ba:	4518                	lw	a4,8(a0)
   116bc:	987caa5b          	0x987caa5b
   116c0:	6249                	lui	tp,0x12
   116c2:	fdbc3397          	auipc	t2,0xfdbc3
   116c6:	565a                	lw	a2,180(sp)
   116c8:	5056                	0x5056
   116ca:	80a8                	0x80a8
   116cc:	7655                	lui	a2,0xffff5
   116ce:	59e0                	lw	s0,116(a1)
   116d0:	e77d                	bnez	a4,117be <rr+0x96>
   116d2:	9a29                	andi	a2,a2,-22
   116d4:	fb7f                	0xfb7f
   116d6:	7a8d                	lui	s5,0xfffe3
   116d8:	0204                	addi	s1,sp,256
   116da:	782e                	flw	fa6,232(sp)
   116dc:	13ff                	0x13ff
   116de:	00ea4d67          	0xea4d67
   116e2:	1310                	addi	a2,sp,416
   116e4:	1206                	slli	tp,tp,0x21
   116e6:	e18e                	fsw	ft3,192(sp)
   116e8:	7f30                	flw	fa2,120(a4)
   116ea:	21f5                	jal	11bd6 <impure_data+0x1ae>
   116ec:	f24f038b          	0xf24f038b
   116f0:	874d                	srai	a4,a4,0x13
   116f2:	052559cf          	0x52559cf
   116f6:	24c5                	jal	119d6 <sig+0x12e>
   116f8:	170d                	addi	a4,a4,-29
   116fa:	addeb52f          	0xaddeb52f
   116fe:	46c9                	li	a3,18
   11700:	90e82c73          	csrrs	s8,0x90e,a6
   11704:	1344ceaf          	0x1344ceaf
   11708:	09f2                	slli	s3,s3,0x1c
   1170a:	6632                	flw	fa2,12(sp)
   1170c:	24bd4fbf 5e4ed04d 	0x5e4ed04d24bd4fbf
   11714:	770a                	flw	fa4,160(sp)
   11716:	0fce                	slli	t6,t6,0x13
   11718:	81f78793          	addi	a5,a5,-2017
   1171c:	e13e                	fsw	fa5,128(sp)
   1171e:	a792                	fsd	ft4,456(sp)
   11720:	bf58                	fsd	fa4,184(a4)
   11722:	9be8a6c7          	fmsub.d	fa3,fa7,ft10,fs3,rdn
   11726:	e1df        	0xa3eb77fae1df

00011728 <rr>:
   11728:	77fa                	flw	fa5,188(sp)
   1172a:	a2aca3eb          	0xa2aca3eb
   1172e:	9db9                	0x9db9
   11730:	d4ae                	sw	a1,104(sp)
   11732:	2c19                	jal	11948 <sig+0xa0>
   11734:	fb5be1e7          	0xfb5be1e7
   11738:	dd38f5fb          	0xdd38f5fb
   1173c:	fdda                	fsw	fs6,248(sp)
   1173e:	d0f4                	sw	a3,100(s1)
   11740:	eb165cd3          	0xeb165cd3
   11744:	7cfe                	flw	fs9,252(sp)
   11746:	546a                	lw	s0,184(sp)
   11748:	0c5c                	addi	a5,sp,532
   1174a:	cd41                	beqz	a0,117e2 <rr+0xba>
   1174c:	73f5cf6b          	0x73f5cf6b
   11750:	bcae                	fsd	fa1,120(sp)
   11752:	1185                	addi	gp,gp,-31
   11754:	da2e2103          	lw	sp,-606(t3)
   11758:	ae26                	fsd	fs1,280(sp)
   1175a:	bab5                	j	110d6 <__errno+0xb4a>
   1175c:	7aba                	flw	fs5,172(sp)
   1175e:	d5f776e7          	0xd5f776e7
   11762:	f49d                	bnez	s1,11690 <n+0xe8>
   11764:	8a29                	andi	a2,a2,10
   11766:	3231                	jal	11072 <__errno+0xae6>
   11768:	85bc                	0x85bc
   1176a:	689a                	flw	fa7,132(sp)
   1176c:	62a9                	lui	t0,0xa
   1176e:	8aa8                	0x8aa8
   11770:	240e                	fld	fs0,192(sp)
   11772:	538c                	lw	a1,32(a5)
   11774:	b61eab77          	0xb61eab77
   11778:	73f2                	flw	ft7,60(sp)
   1177a:	9ccd                	0x9ccd
   1177c:	c81a                	sw	t1,16(sp)
   1177e:	ac0e6563          	bltu	t3,zero,10a48 <__errno+0x4bc>
   11782:	6c65                	lui	s8,0x19
   11784:	90b209bf e642e25e 	0xe642e25e90b209bf
   1178c:	1549                	addi	a0,a0,-14
   1178e:	7e35                	lui	t3,0xfffed
   11790:	1830                	addi	a2,sp,56
   11792:	879a                	mv	a5,t1
   11794:	bb02                	fsd	ft0,432(sp)
   11796:	c75c                	sw	a5,12(a4)
   11798:	2362                	fld	ft6,24(sp)
   1179a:	e011                	bnez	s0,1179e <rr+0x76>
   1179c:	405f ebc2 7990      	0x7990ebc2405f
   117a2:	01dc                	addi	a5,sp,196
   117a4:	3d3d07f3          	0x3d3d07f3
   117a8:	a5be                	fsd	fa5,200(sp)
   117aa:	c5b9                	beqz	a1,117f8 <rr+0xd0>
   117ac:	98d8cc33          	0x98d8cc33
   117b0:	e108                	fsw	fa0,0(a0)
   117b2:	dd65                	beqz	a0,117aa <rr+0x82>
   117b4:	ce301343          	fmadd.q	ft6,ft0,ft3,fs9,rtz
   117b8:	0dbdc0cb          	0xdbdc0cb
   117bc:	b9ca                	fsd	fs2,240(sp)
   117be:	c204                	sw	s1,0(a2)
   117c0:	1810                	addi	a2,sp,48
   117c2:	eabe                	fsw	fa5,84(sp)
   117c4:	163a                	slli	a2,a2,0x2e
   117c6:	9849                	andi	s0,s0,-14
   117c8:	234c8ff7          	0x234c8ff7
   117cc:	9bc14e3b          	0x9bc14e3b
   117d0:	2226                	fld	ft4,72(sp)
   117d2:	4b4c                	lw	a1,20(a4)
   117d4:	83be                	mv	t2,a5
   117d6:	0798                	addi	a4,sp,960
   117d8:	c5f5                	beqz	a1,118c4 <sig+0x1c>
   117da:	ba59                	j	11170 <__errno+0xbe4>
   117dc:	d9c77317          	auipc	t1,0xd9c77
   117e0:	89f5                	andi	a1,a1,29
   117e2:	1ce6                	slli	s9,s9,0x39
   117e4:	9af5                	andi	a3,a3,-3
   117e6:	05f4                	addi	a3,sp,716
   117e8:	d42a                	sw	a0,40(sp)
   117ea:	b5ca7a83          	0xb5ca7a83
   117ee:	c509                	beqz	a0,117f8 <rr+0xd0>
   117f0:	a95f 0811 20a2      	0x20a20811a95f
   117f6:	0935                	addi	s2,s2,13
   117f8:	9941                	andi	a0,a0,-16
   117fa:	7364                	flw	fs1,100(a4)
   117fc:	1ef5                	addi	t4,t4,-3
   117fe:	d969                	beqz	a0,117d0 <rr+0xa8>
   11800:	ec0d                	bnez	s0,1183a <rr+0x112>
   11802:	6878                	flw	fa4,84(s0)
   11804:	add6                	fsd	fs5,216(sp)
   11806:	d8b74043          	fmadd.s	ft0,fa4,fa1,fs11,rmm
   1180a:	7516                	flw	fa0,100(sp)
   1180c:	70ff                	0x70ff
   1180e:	5c70                	lw	a2,124(s0)
   11810:	2e1d                	jal	11b46 <impure_data+0x11e>
   11812:	4ce5                	li	s9,25
   11814:	f209e123          	0xf209e123
   11818:	19c4                	addi	s1,sp,244
   1181a:	620afe43          	fmadd.d	ft8,fs5,ft0,fa2
   1181e:	9774                	0x9774
   11820:	7a58d047          	fmsub.d	ft0,fa7,ft5,fa5,unknown
   11824:	524b09b7          	lui	s3,0x524b0
   11828:	f044                	fsw	fs1,36(s0)
   1182a:	44a296cb          	0x44a296cb
   1182e:	2a90                	fld	fa2,16(a3)
   11830:	95dc                	0x95dc
   11832:	5149                	li	sp,-14
   11834:	3ed6                	fld	ft9,368(sp)
   11836:	e4b8                	fsw	fa4,72(s1)
   11838:	e300                	fsw	fs0,0(a4)
   1183a:	d4f8d21b          	0xd4f8d21b
   1183e:	2966                	fld	fs2,88(sp)
   11840:	19c4                	addi	s1,sp,244
   11842:	d9ee                	sw	s11,240(sp)
   11844:	88f6                	mv	a7,t4
   11846:	74abb607          	fld	fa2,1866(s7) # fffe774a <__BSS_END__+0xfffd58ce>
   1184a:	f8d0                	fsw	fa2,52(s1)
   1184c:	3295                	jal	111b0 <__errno+0xc24>
   1184e:	a7e1                	j	12016 <__BSS_END__+0x19a>
   11850:	8edc                	0x8edc
   11852:	9371                	srli	a4,a4,0x3c
   11854:	c096                	sw	t0,64(sp)
   11856:	ba9f fbbc 0ad2      	0xad2fbbcba9f
   1185c:	9fe0c363          	blt	ra,t5,10a42 <__errno+0x4b6>
   11860:	10b4                	addi	a3,sp,104
   11862:	472a                	lw	a4,136(sp)
   11864:	da9c946b          	0xda9c946b
   11868:	37276997          	auipc	s3,0x37276
   1186c:	52fc                	lw	a5,100(a3)
   1186e:	04e4                	addi	s1,sp,588
   11870:	33b5                	jal	115dc <n+0x34>
   11872:	d192                	sw	tp,224(sp)
   11874:	ef0e                	fsw	ft3,156(sp)
   11876:	9ddda277          	0x9ddda277
   1187a:	4961                	li	s2,24
   1187c:	2d56                	fld	fs10,336(sp)
   1187e:	b582                	fsd	ft0,232(sp)
   11880:	6ca4d02f          	0x6ca4d02f
   11884:	7d0c0fc3          	0x7d0c0fc3
   11888:	96e2                	add	a3,a3,s8
   1188a:	a291                	j	119ce <sig+0x126>
   1188c:	b6988a4f          	fnmadd.q	fs4,fa7,fs1,fs6,rne
   11890:	7552                	flw	fa0,52(sp)
   11892:	3c24785b          	0x3c24785b
   11896:	eaee                	fsw	fs11,84(sp)
   11898:	3424                	fld	fs1,104(s0)
   1189a:	8799                	srai	a5,a5,0x6
   1189c:	fcb49693          	0xfcb49693
   118a0:	4d84                	lw	s1,24(a1)
   118a2:	21e6                	fld	ft3,88(sp)
   118a4:	cea8                	sw	a0,88(a3)
   118a6:	9e2d                	0x9e2d

000118a8 <sig>:
   118a8:	ceb7e983          	0xceb7e983
   118ac:	b200                	fsd	fs0,32(a2)
   118ae:	3989e693          	ori	a3,s3,920
   118b2:	f915                	bnez	a0,117e6 <rr+0xbe>
   118b4:	9599                	srai	a1,a1,0x26
   118b6:	cf89                	beqz	a5,118d0 <sig+0x28>
   118b8:	9fae                	add	t6,t6,a1
   118ba:	1ec0                	addi	s0,sp,884
   118bc:	f2f88007          	0xf2f88007
   118c0:	eed5                	bnez	a3,1197c <sig+0xd4>
   118c2:	2a24                	fld	fs1,80(a2)
   118c4:	7c4e                	flw	fs8,240(sp)
   118c6:	53b29c5b          	0x53b29c5b
   118ca:	21a1                	jal	11d12 <impure_data+0x2ea>
   118cc:	83ae                	mv	t2,a1
   118ce:	af75                	j	1208a <__BSS_END__+0x20e>
   118d0:	d694                	sw	a3,40(a3)
   118d2:	04fd                	addi	s1,s1,31
   118d4:	7550094b          	0x7550094b
   118d8:	9ac4                	0x9ac4
   118da:	b2a6                	fsd	fs1,352(sp)
   118dc:	8022                	c.mv	zero,s0
   118de:	e49d                	bnez	s1,1190c <sig+0x64>
   118e0:	f162                	fsw	fs8,160(sp)
   118e2:	7ed6                	flw	ft9,116(sp)
   118e4:	14bb3a1b          	0x14bb3a1b
   118e8:	d8dd                	beqz	s1,1189e <rr+0x176>
   118ea:	bb29                	j	11604 <n+0x5c>
   118ec:	15c2                	slli	a1,a1,0x30
   118ee:	5c58                	lw	a4,60(s0)
   118f0:	d848                	sw	a0,52(s0)
   118f2:	7a80                	flw	fs0,48(a3)
   118f4:	f449                	bnez	s0,1187e <rr+0x156>
   118f6:	b122                	fsd	fs0,160(sp)
   118f8:	a808                	fsd	fa0,16(s0)
   118fa:	59dc                	lw	a5,52(a1)
   118fc:	43e2                	lw	t2,24(sp)
   118fe:	bc14                	fsd	fa3,56(s0)
   11900:	e304ff93          	andi	t6,s1,-464
   11904:	cc97ee4b          	0xcc97ee4b
   11908:	42ef6b57          	0x42ef6b57
   1190c:	839f 1436 0b45      	0xb451436839f
   11912:	ae86                	fsd	ft1,344(sp)
   11914:	6a843a17          	auipc	s4,0x6a843
   11918:	fb91                	bnez	a5,1182c <rr+0x104>
   1191a:	2381                	jal	11e5a <d0inv+0x2>
   1191c:	0635                	addi	a2,a2,13
   1191e:	09fd                	addi	s3,s3,31
   11920:	a431aac3          	0xa431aac3
   11924:	0269                	addi	tp,tp,26
   11926:	d722                	sw	s0,172(sp)
   11928:	df3e2697          	auipc	a3,0xdf3e2
   1192c:	915e                	add	sp,sp,s7
   1192e:	35e2                	fld	fa1,56(sp)
   11930:	6956                	flw	fs2,84(sp)
   11932:	edba                	fsw	fa4,216(sp)
   11934:	7448                	flw	fa0,44(s0)
   11936:	1d38                	addi	a4,sp,696
   11938:	06df 9300 5f00      	0x5f00930006df
   1193e:	961e                	add	a2,a2,t2
   11940:	e960                	fsw	fs0,84(a0)
   11942:	4addf2a7          	0x4addf2a7
   11946:	884e                	mv	a6,s3
   11948:	76b1                	lui	a3,0xfffec
   1194a:	7dfe                	flw	fs11,252(sp)
   1194c:	aa79                	j	11aea <impure_data+0xc2>
   1194e:	4079                	c.li	zero,30
   11950:	378d                	jal	118b2 <sig+0xa>
   11952:	1f3a                	slli	t5,t5,0x2e
   11954:	96c20697          	auipc	a3,0x96c20
   11958:	268aea57          	0x268aea57
   1195c:	69a4                	flw	fs1,80(a1)
   1195e:	2c85                	jal	11bce <impure_data+0x1a6>
   11960:	f512                	fsw	ft4,168(sp)
   11962:	0474                	addi	a3,sp,524
   11964:	555c                	lw	a5,44(a0)
   11966:	2388                	fld	fa0,0(a5)
   11968:	58679953          	0x58679953
   1196c:	a3a0                	fsd	fs0,64(a5)
   1196e:	e73d                	bnez	a4,119dc <sig+0x134>
   11970:	1b9a                	slli	s7,s7,0x26
   11972:	04d34343          	0x4d34343
   11976:	699f e066 fc0b      	0xfc0be066699f
   1197c:	06f2                	slli	a3,a3,0x1c
   1197e:	cce6                	sw	s9,88(sp)
   11980:	dfa0                	sw	s0,120(a5)
   11982:	d94c                	sw	a1,52(a0)
   11984:	6c1ddca3          	0x6c1ddca3
   11988:	11f6                	slli	gp,gp,0x3d
   1198a:	e96c                	fsw	fa1,84(a0)
   1198c:	5db4                	lw	a3,120(a1)
   1198e:	4f69fc63          	bgeu	s3,s6,11e86 <__BSS_END__+0xa>
   11992:	c3e73bdb          	0xc3e73bdb
   11996:	a621                	j	11c9e <impure_data+0x276>
   11998:	2111                	jal	11d9c <impure_data+0x374>
   1199a:	9f29                	0x9f29
   1199c:	b86e1e6b          	0xb86e1e6b
   119a0:	b74f923b          	0xb74f923b
   119a4:	67a0                	flw	fs0,72(a5)
   119a6:	5929                	li	s2,-22
   119a8:	097f                	0x97f
   119aa:	c412                	sw	tp,8(sp)
   119ac:	8c1c8ca7          	0x8c1c8ca7
   119b0:	cdb6                	sw	a3,216(sp)
   119b2:	fe0f494f          	fnmadd.q	fs2,ft10,ft0,ft11,rmm
   119b6:	87c5                	srai	a5,a5,0x11
   119b8:	1aee                	slli	s5,s5,0x3b
   119ba:	50c0                	lw	s0,36(s1)
   119bc:	368e                	fld	fa3,224(sp)
   119be:	8a26                	mv	s4,s1
   119c0:	2232                	fld	ft4,264(sp)
   119c2:	eaf1                	bnez	a3,11a96 <impure_data+0x6e>
   119c4:	e4d8                	fsw	fa4,12(s1)
   119c6:	7dad                	lui	s11,0xfffeb
   119c8:	2ac6                	fld	fs5,80(sp)
   119ca:	8aaa39eb          	0x8aaa39eb
   119ce:	08ca744f          	fnmadd.s	fs0,fs4,fa2,ft1
   119d2:	f349                	bnez	a4,11954 <sig+0xac>
   119d4:	656c                	flw	fa1,76(a0)
   119d6:	1e0c                	addi	a1,sp,816
   119d8:	4e29                	li	t3,10
   119da:	e96d                	bnez	a0,11acc <impure_data+0xa4>
   119dc:	d194                	sw	a3,32(a1)
   119de:	8575                	srai	a0,a0,0x1d
   119e0:	bd31                	j	117fc <rr+0xd4>
   119e2:	e439                	bnez	s0,11a30 <impure_data+0x8>
   119e4:	a74a77e3          	bgeu	s4,s4,11452 <__errno+0xec6>
   119e8:	5b88                	lw	a0,48(a5)
   119ea:	0f46                	slli	t5,t5,0x11
   119ec:	1152                	slli	sp,sp,0x34
   119ee:	f4e2                	fsw	fs8,104(sp)
   119f0:	0ad8                	addi	a4,sp,340
   119f2:	8040                	0x8040
   119f4:	01ec                	addi	a1,sp,204
   119f6:	e585                	bnez	a1,11a1e <sig+0x176>
   119f8:	7536                	flw	fa0,108(sp)
   119fa:	a29d                	j	11b60 <impure_data+0x138>
   119fc:	9326                	add	t1,t1,s1
   119fe:	55c1                	li	a1,-16
   11a00:	c63e                	sw	a5,12(sp)
   11a02:	5aee9ebb          	0x5aee9ebb
   11a06:	83d720c7          	fmsub.d	ft1,fa4,ft9,fa6,rdn
   11a0a:	dba5ef67          	0xdba5ef67
   11a0e:	59ff                	0x59ff
   11a10:	879b937b          	0x879b937b
   11a14:	c74c                	sw	a1,12(a4)
   11a16:	43a5                	li	t2,9
   11a18:	f825                	bnez	s0,11988 <sig+0xe0>
   11a1a:	82b8                	0x82b8
   11a1c:	4b3a                	lw	s6,140(sp)
   11a1e:	fdf0                	fsw	fa2,124(a1)
   11a20:	2fbe                	fld	ft11,456(sp)
   11a22:	8fc6                	mv	t6,a7
   11a24:	6da5                	lui	s11,0x9
   11a26:	114e                	slli	sp,sp,0x33

00011a28 <impure_data>:
   11a28:	0000                	unimp
   11a2a:	0000                	unimp
   11a2c:	1d14                	addi	a3,sp,688
   11a2e:	0001                	nop
   11a30:	1d7c                	addi	a5,sp,700
   11a32:	0001                	nop
   11a34:	1de4                	addi	s1,sp,764
   11a36:	0001                	nop
	...
   11ad0:	0001                	nop
   11ad2:	0000                	unimp
   11ad4:	0000                	unimp
   11ad6:	0000                	unimp
   11ad8:	330e                	fld	ft6,224(sp)
   11ada:	abcd                	j	120cc <__BSS_END__+0x250>
   11adc:	1234                	addi	a3,sp,296
   11ade:	e66d                	bnez	a2,11bc8 <impure_data+0x1a0>
   11ae0:	deec                	sw	a1,124(a3)
   11ae2:	0005                	c.nop	1
   11ae4:	0000000b          	0xb
	...

Disassembly of section .sdata:

00011e50 <_global_impure_ptr>:
   11e50:	1a28                	addi	a0,sp,312
   11e52:	0001                	nop

00011e54 <__dso_handle>:
   11e54:	0000                	unimp
	...

00011e58 <d0inv>:
   11e58:	71df f09b       	0x1a28f09b71df

00011e5c <_impure_ptr>:
   11e5c:	1a28                	addi	a0,sp,312
   11e5e:	0001                	nop

Disassembly of section .bss:

00011e60 <__bss_start>:
   11e60:	0000                	unimp
	...

00011e64 <object.0>:
	...

Disassembly of section .comment:

00000000 <.comment>:
   0:	3a434347          	fmsub.d	ft6,ft6,ft4,ft7,rmm
   4:	2820                	fld	fs0,80(s0)
   6:	29554e47          	fmsub.s	ft8,fa0,fs5,ft5,rmm
   a:	3120                	fld	fs0,96(a0)
   c:	2e30                	fld	fa2,88(a2)
   e:	2e32                	fld	ft8,264(sp)
  10:	0030                	addi	a2,sp,8

Disassembly of section .riscv.attributes:

00000000 <.riscv.attributes>:
   0:	3441                	jal	fffffa80 <__BSS_END__+0xfffedc04>
   2:	0000                	unimp
   4:	7200                	flw	fs0,32(a2)
   6:	7369                	lui	t1,0xffffa
   8:	01007663          	bgeu	zero,a6,14 <main-0x10060>
   c:	002a                	c.slli	zero,0xa
   e:	0000                	unimp
  10:	1004                	addi	s1,sp,32
  12:	7205                	lui	tp,0xfffe1
  14:	3376                	fld	ft6,376(sp)
  16:	6932                	flw	fs2,12(sp)
  18:	7032                	flw	ft0,44(sp)
  1a:	5f30                	lw	a2,120(a4)
  1c:	326d                	jal	fffff9c6 <__BSS_END__+0xfffedb4a>
  1e:	3070                	fld	fa2,224(s0)
  20:	615f 7032 5f30      	0x5f307032615f
  26:	3266                	fld	ft4,120(sp)
  28:	3070                	fld	fa2,224(s0)
  2a:	645f 7032 5f30      	0x5f307032645f
  30:	30703263          	0x30703263
	...
