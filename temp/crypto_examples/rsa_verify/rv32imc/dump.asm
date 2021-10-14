
rsa_rv.elf:     file format elf32-littleriscv


Disassembly of section .text:

00010074 <main>:
   10074:	0b01a503          	lw	a0,176(gp) # 11ec8 <d0inv>
   10078:	b7010113          	addi	sp,sp,-1168
   1007c:	0310                	addi	a2,sp,384
   1007e:	858a                	mv	a1,sp
   10080:	48112623          	sw	ra,1164(sp)
   10084:	2491                	jal	102c8 <mod_pow.constprop.0>
   10086:	48c12083          	lw	ra,1164(sp)
   1008a:	4501                	li	a0,0
   1008c:	49010113          	addi	sp,sp,1168
   10090:	8082                	ret

00010092 <register_fini>:
   10092:	00000793          	li	a5,0
   10096:	c791                	beqz	a5,100a2 <register_fini+0x10>
   10098:	00000517          	auipc	a0,0x0
   1009c:	49850513          	addi	a0,a0,1176 # 10530 <__libc_fini_array>
   100a0:	a1e1                	j	10568 <atexit>
   100a2:	8082                	ret

000100a4 <_start>:
   100a4:	00002197          	auipc	gp,0x2
   100a8:	d7418193          	addi	gp,gp,-652 # 11e18 <__global_pointer$>
   100ac:	0b818513          	addi	a0,gp,184 # 11ed0 <completed.1>
   100b0:	0d418613          	addi	a2,gp,212 # 11eec <__BSS_END__>
   100b4:	8e09                	sub	a2,a2,a0
   100b6:	4581                	li	a1,0
   100b8:	2e09                	jal	103ca <memset>
   100ba:	00000517          	auipc	a0,0x0
   100be:	4ae50513          	addi	a0,a0,1198 # 10568 <atexit>
   100c2:	c511                	beqz	a0,100ce <_start+0x2a>
   100c4:	00000517          	auipc	a0,0x0
   100c8:	46c50513          	addi	a0,a0,1132 # 10530 <__libc_fini_array>
   100cc:	2971                	jal	10568 <atexit>
   100ce:	2c49                	jal	10360 <__libc_init_array>
   100d0:	4502                	lw	a0,0(sp)
   100d2:	004c                	addi	a1,sp,4
   100d4:	4601                	li	a2,0
   100d6:	3f79                	jal	10074 <main>
   100d8:	a4bd                	j	10346 <exit>

000100da <__do_global_dtors_aux>:
   100da:	1141                	addi	sp,sp,-16
   100dc:	c422                	sw	s0,8(sp)
   100de:	0b818413          	addi	s0,gp,184 # 11ed0 <completed.1>
   100e2:	00044783          	lbu	a5,0(s0)
   100e6:	c606                	sw	ra,12(sp)
   100e8:	ef99                	bnez	a5,10106 <__do_global_dtors_aux+0x2c>
   100ea:	00000793          	li	a5,0
   100ee:	cb89                	beqz	a5,10100 <__do_global_dtors_aux+0x26>
   100f0:	00001517          	auipc	a0,0x1
   100f4:	51450513          	addi	a0,a0,1300 # 11604 <__FRAME_END__>
   100f8:	00000097          	auipc	ra,0x0
   100fc:	000000e7          	jalr	zero # 0 <main-0x10074>
   10100:	4785                	li	a5,1
   10102:	00f40023          	sb	a5,0(s0)
   10106:	40b2                	lw	ra,12(sp)
   10108:	4422                	lw	s0,8(sp)
   1010a:	0141                	addi	sp,sp,16
   1010c:	8082                	ret

0001010e <frame_dummy>:
   1010e:	00000793          	li	a5,0
   10112:	cb99                	beqz	a5,10128 <frame_dummy+0x1a>
   10114:	0bc18593          	addi	a1,gp,188 # 11ed4 <object.0>
   10118:	00001517          	auipc	a0,0x1
   1011c:	4ec50513          	addi	a0,a0,1260 # 11604 <__FRAME_END__>
   10120:	00000317          	auipc	t1,0x0
   10124:	00000067          	jr	zero # 0 <main-0x10074>
   10128:	8082                	ret

0001012a <ge_mod.constprop.0>:
   1012a:	65c5                	lui	a1,0x11
   1012c:	61858793          	addi	a5,a1,1560 # 11618 <n>
   10130:	17c50513          	addi	a0,a0,380
   10134:	17c78793          	addi	a5,a5,380
   10138:	61858593          	addi	a1,a1,1560
   1013c:	a031                	j	10148 <ge_mod.constprop.0+0x1e>
   1013e:	00d76e63          	bltu	a4,a3,1015a <ge_mod.constprop.0+0x30>
   10142:	00b78c63          	beq	a5,a1,1015a <ge_mod.constprop.0+0x30>
   10146:	87b2                	mv	a5,a2
   10148:	4114                	lw	a3,0(a0)
   1014a:	4398                	lw	a4,0(a5)
   1014c:	ffc78613          	addi	a2,a5,-4
   10150:	1571                	addi	a0,a0,-4
   10152:	fee6f6e3          	bgeu	a3,a4,1013e <ge_mod.constprop.0+0x14>
   10156:	4501                	li	a0,0
   10158:	8082                	ret
   1015a:	4505                	li	a0,1
   1015c:	8082                	ret

0001015e <sub_mod.constprop.0>:
   1015e:	6645                	lui	a2,0x11
   10160:	61860613          	addi	a2,a2,1560 # 11618 <n>
   10164:	18060813          	addi	a6,a2,384
   10168:	4781                	li	a5,0
   1016a:	4581                	li	a1,0
   1016c:	4118                	lw	a4,0(a0)
   1016e:	4214                	lw	a3,0(a2)
   10170:	0611                	addi	a2,a2,4
   10172:	97ba                	add	a5,a5,a4
   10174:	40d786b3          	sub	a3,a5,a3
   10178:	00e7b733          	sltu	a4,a5,a4
   1017c:	972e                	add	a4,a4,a1
   1017e:	00d7b7b3          	sltu	a5,a5,a3
   10182:	c114                	sw	a3,0(a0)
   10184:	40f707b3          	sub	a5,a4,a5
   10188:	41f7d593          	srai	a1,a5,0x1f
   1018c:	0511                	addi	a0,a0,4
   1018e:	fcc81fe3          	bne	a6,a2,1016c <sub_mod.constprop.0+0xe>
   10192:	8082                	ret

00010194 <mul32>:
   10194:	87ae                	mv	a5,a1
   10196:	02b535b3          	mulhu	a1,a0,a1
   1019a:	02f50533          	mul	a0,a0,a5
   1019e:	8082                	ret

000101a0 <mula32>:
   101a0:	02b507b3          	mul	a5,a0,a1
   101a4:	02b535b3          	mulhu	a1,a0,a1
   101a8:	00c78533          	add	a0,a5,a2
   101ac:	00f537b3          	sltu	a5,a0,a5
   101b0:	95be                	add	a1,a1,a5
   101b2:	8082                	ret

000101b4 <mulaa32>:
   101b4:	02b50733          	mul	a4,a0,a1
   101b8:	96b2                	add	a3,a3,a2
   101ba:	00c6b633          	sltu	a2,a3,a2
   101be:	02b537b3          	mulhu	a5,a0,a1
   101c2:	00d70533          	add	a0,a4,a3
   101c6:	00e535b3          	sltu	a1,a0,a4
   101ca:	97b2                	add	a5,a5,a2
   101cc:	95be                	add	a1,a1,a5
   101ce:	8082                	ret

000101d0 <mont_mul_add.constprop.0>:
   101d0:	7179                	addi	sp,sp,-48
   101d2:	c85a                	sw	s6,16(sp)
   101d4:	8b2e                	mv	s6,a1
   101d6:	c65e                	sw	s7,12(sp)
   101d8:	428c                	lw	a1,0(a3)
   101da:	8bb2                	mv	s7,a2
   101dc:	000b2603          	lw	a2,0(s6)
   101e0:	ca56                	sw	s5,20(sp)
   101e2:	8aaa                	mv	s5,a0
   101e4:	855e                	mv	a0,s7
   101e6:	d606                	sw	ra,44(sp)
   101e8:	d422                	sw	s0,40(sp)
   101ea:	d226                	sw	s1,36(sp)
   101ec:	d04a                	sw	s2,32(sp)
   101ee:	ce4e                	sw	s3,28(sp)
   101f0:	cc52                	sw	s4,24(sp)
   101f2:	c462                	sw	s8,8(sp)
   101f4:	8a36                	mv	s4,a3
   101f6:	376d                	jal	101a0 <mula32>
   101f8:	03550ab3          	mul	s5,a0,s5
   101fc:	6c45                	lui	s8,0x11
   101fe:	618c0c13          	addi	s8,s8,1560 # 11618 <n>
   10202:	842e                	mv	s0,a1
   10204:	000c2583          	lw	a1,0(s8)
   10208:	862a                	mv	a2,a0
   1020a:	004c0913          	addi	s2,s8,4
   1020e:	0a11                	addi	s4,s4,4
   10210:	89da                	mv	s3,s6
   10212:	180c0c13          	addi	s8,s8,384
   10216:	8556                	mv	a0,s5
   10218:	3761                	jal	101a0 <mula32>
   1021a:	84ae                	mv	s1,a1
   1021c:	0049a603          	lw	a2,4(s3)
   10220:	000a2583          	lw	a1,0(s4)
   10224:	86a2                	mv	a3,s0
   10226:	855e                	mv	a0,s7
   10228:	3771                	jal	101b4 <mulaa32>
   1022a:	842e                	mv	s0,a1
   1022c:	00092583          	lw	a1,0(s2)
   10230:	862a                	mv	a2,a0
   10232:	86a6                	mv	a3,s1
   10234:	8556                	mv	a0,s5
   10236:	3fbd                	jal	101b4 <mulaa32>
   10238:	00a9a023          	sw	a0,0(s3)
   1023c:	0911                	addi	s2,s2,4
   1023e:	84ae                	mv	s1,a1
   10240:	0a11                	addi	s4,s4,4
   10242:	0991                	addi	s3,s3,4
   10244:	fd2c1ce3          	bne	s8,s2,1021c <mont_mul_add.constprop.0+0x4c>
   10248:	942e                	add	s0,s0,a1
   1024a:	168b2e23          	sw	s0,380(s6)
   1024e:	00b46e63          	bltu	s0,a1,1026a <mont_mul_add.constprop.0+0x9a>
   10252:	50b2                	lw	ra,44(sp)
   10254:	5422                	lw	s0,40(sp)
   10256:	5492                	lw	s1,36(sp)
   10258:	5902                	lw	s2,32(sp)
   1025a:	49f2                	lw	s3,28(sp)
   1025c:	4a62                	lw	s4,24(sp)
   1025e:	4ad2                	lw	s5,20(sp)
   10260:	4b42                	lw	s6,16(sp)
   10262:	4bb2                	lw	s7,12(sp)
   10264:	4c22                	lw	s8,8(sp)
   10266:	6145                	addi	sp,sp,48
   10268:	8082                	ret
   1026a:	5422                	lw	s0,40(sp)
   1026c:	50b2                	lw	ra,44(sp)
   1026e:	5492                	lw	s1,36(sp)
   10270:	5902                	lw	s2,32(sp)
   10272:	49f2                	lw	s3,28(sp)
   10274:	4a62                	lw	s4,24(sp)
   10276:	4ad2                	lw	s5,20(sp)
   10278:	4bb2                	lw	s7,12(sp)
   1027a:	4c22                	lw	s8,8(sp)
   1027c:	855a                	mv	a0,s6
   1027e:	4b42                	lw	s6,16(sp)
   10280:	6145                	addi	sp,sp,48
   10282:	bdf1                	j	1015e <sub_mod.constprop.0>

00010284 <mont_mul.constprop.0>:
   10284:	1101                	addi	sp,sp,-32
   10286:	ca26                	sw	s1,20(sp)
   10288:	84ae                	mv	s1,a1
   1028a:	cc22                	sw	s0,24(sp)
   1028c:	c64e                	sw	s3,12(sp)
   1028e:	8432                	mv	s0,a2
   10290:	89aa                	mv	s3,a0
   10292:	18000613          	li	a2,384
   10296:	4581                	li	a1,0
   10298:	8526                	mv	a0,s1
   1029a:	c84a                	sw	s2,16(sp)
   1029c:	c452                	sw	s4,8(sp)
   1029e:	ce06                	sw	ra,28(sp)
   102a0:	8936                	mv	s2,a3
   102a2:	18040a13          	addi	s4,s0,384
   102a6:	2215                	jal	103ca <memset>
   102a8:	4010                	lw	a2,0(s0)
   102aa:	86ca                	mv	a3,s2
   102ac:	0411                	addi	s0,s0,4
   102ae:	85a6                	mv	a1,s1
   102b0:	854e                	mv	a0,s3
   102b2:	3f39                	jal	101d0 <mont_mul_add.constprop.0>
   102b4:	fe8a1ae3          	bne	s4,s0,102a8 <mont_mul.constprop.0+0x24>
   102b8:	40f2                	lw	ra,28(sp)
   102ba:	4462                	lw	s0,24(sp)
   102bc:	44d2                	lw	s1,20(sp)
   102be:	4942                	lw	s2,16(sp)
   102c0:	49b2                	lw	s3,12(sp)
   102c2:	4a22                	lw	s4,8(sp)
   102c4:	6105                	addi	sp,sp,32
   102c6:	8082                	ret

000102c8 <mod_pow.constprop.0>:
   102c8:	66c5                	lui	a3,0x11
   102ca:	1101                	addi	sp,sp,-32
   102cc:	61868693          	addi	a3,a3,1560 # 11618 <n>
   102d0:	cc22                	sw	s0,24(sp)
   102d2:	c256                	sw	s5,4(sp)
   102d4:	8432                	mv	s0,a2
   102d6:	30068a93          	addi	s5,a3,768
   102da:	c452                	sw	s4,8(sp)
   102dc:	18068693          	addi	a3,a3,384
   102e0:	8a2e                	mv	s4,a1
   102e2:	8656                	mv	a2,s5
   102e4:	85a2                	mv	a1,s0
   102e6:	ca26                	sw	s1,20(sp)
   102e8:	c84a                	sw	s2,16(sp)
   102ea:	c64e                	sw	s3,12(sp)
   102ec:	ce06                	sw	ra,28(sp)
   102ee:	89aa                	mv	s3,a0
   102f0:	18040913          	addi	s2,s0,384
   102f4:	3f41                	jal	10284 <mont_mul.constprop.0>
   102f6:	44a1                	li	s1,8
   102f8:	86a2                	mv	a3,s0
   102fa:	8622                	mv	a2,s0
   102fc:	85ca                	mv	a1,s2
   102fe:	854e                	mv	a0,s3
   10300:	3751                	jal	10284 <mont_mul.constprop.0>
   10302:	14fd                	addi	s1,s1,-1
   10304:	86ca                	mv	a3,s2
   10306:	864a                	mv	a2,s2
   10308:	85a2                	mv	a1,s0
   1030a:	854e                	mv	a0,s3
   1030c:	3fa5                	jal	10284 <mont_mul.constprop.0>
   1030e:	f4ed                	bnez	s1,102f8 <mod_pow.constprop.0+0x30>
   10310:	854e                	mv	a0,s3
   10312:	86d6                	mv	a3,s5
   10314:	8622                	mv	a2,s0
   10316:	85d2                	mv	a1,s4
   10318:	37b5                	jal	10284 <mont_mul.constprop.0>
   1031a:	8552                	mv	a0,s4
   1031c:	3539                	jal	1012a <ge_mod.constprop.0>
   1031e:	e911                	bnez	a0,10332 <mod_pow.constprop.0+0x6a>
   10320:	40f2                	lw	ra,28(sp)
   10322:	4462                	lw	s0,24(sp)
   10324:	44d2                	lw	s1,20(sp)
   10326:	4942                	lw	s2,16(sp)
   10328:	49b2                	lw	s3,12(sp)
   1032a:	4a22                	lw	s4,8(sp)
   1032c:	4a92                	lw	s5,4(sp)
   1032e:	6105                	addi	sp,sp,32
   10330:	8082                	ret
   10332:	4462                	lw	s0,24(sp)
   10334:	40f2                	lw	ra,28(sp)
   10336:	44d2                	lw	s1,20(sp)
   10338:	4942                	lw	s2,16(sp)
   1033a:	49b2                	lw	s3,12(sp)
   1033c:	4a92                	lw	s5,4(sp)
   1033e:	8552                	mv	a0,s4
   10340:	4a22                	lw	s4,8(sp)
   10342:	6105                	addi	sp,sp,32
   10344:	bd29                	j	1015e <sub_mod.constprop.0>

00010346 <exit>:
   10346:	1141                	addi	sp,sp,-16
   10348:	4581                	li	a1,0
   1034a:	c422                	sw	s0,8(sp)
   1034c:	c606                	sw	ra,12(sp)
   1034e:	842a                	mv	s0,a0
   10350:	220d                	jal	10472 <__call_exitprocs>
   10352:	0a81a503          	lw	a0,168(gp) # 11ec0 <_global_impure_ptr>
   10356:	5d5c                	lw	a5,60(a0)
   10358:	c391                	beqz	a5,1035c <exit+0x16>
   1035a:	9782                	jalr	a5
   1035c:	8522                	mv	a0,s0
   1035e:	2441                	jal	105de <_exit>

00010360 <__libc_init_array>:
   10360:	1141                	addi	sp,sp,-16
   10362:	c422                	sw	s0,8(sp)
   10364:	c04a                	sw	s2,0(sp)
   10366:	00001417          	auipc	s0,0x1
   1036a:	2a240413          	addi	s0,s0,674 # 11608 <__init_array_start>
   1036e:	00001917          	auipc	s2,0x1
   10372:	29a90913          	addi	s2,s2,666 # 11608 <__init_array_start>
   10376:	40890933          	sub	s2,s2,s0
   1037a:	c606                	sw	ra,12(sp)
   1037c:	c226                	sw	s1,4(sp)
   1037e:	40295913          	srai	s2,s2,0x2
   10382:	00090963          	beqz	s2,10394 <__libc_init_array+0x34>
   10386:	4481                	li	s1,0
   10388:	401c                	lw	a5,0(s0)
   1038a:	0485                	addi	s1,s1,1
   1038c:	0411                	addi	s0,s0,4
   1038e:	9782                	jalr	a5
   10390:	fe991ce3          	bne	s2,s1,10388 <__libc_init_array+0x28>
   10394:	00001417          	auipc	s0,0x1
   10398:	27440413          	addi	s0,s0,628 # 11608 <__init_array_start>
   1039c:	00001917          	auipc	s2,0x1
   103a0:	27490913          	addi	s2,s2,628 # 11610 <__do_global_dtors_aux_fini_array_entry>
   103a4:	40890933          	sub	s2,s2,s0
   103a8:	40295913          	srai	s2,s2,0x2
   103ac:	00090963          	beqz	s2,103be <__libc_init_array+0x5e>
   103b0:	4481                	li	s1,0
   103b2:	401c                	lw	a5,0(s0)
   103b4:	0485                	addi	s1,s1,1
   103b6:	0411                	addi	s0,s0,4
   103b8:	9782                	jalr	a5
   103ba:	fe991ce3          	bne	s2,s1,103b2 <__libc_init_array+0x52>
   103be:	40b2                	lw	ra,12(sp)
   103c0:	4422                	lw	s0,8(sp)
   103c2:	4492                	lw	s1,4(sp)
   103c4:	4902                	lw	s2,0(sp)
   103c6:	0141                	addi	sp,sp,16
   103c8:	8082                	ret

000103ca <memset>:
   103ca:	433d                	li	t1,15
   103cc:	872a                	mv	a4,a0
   103ce:	02c37363          	bgeu	t1,a2,103f4 <memset+0x2a>
   103d2:	00f77793          	andi	a5,a4,15
   103d6:	efbd                	bnez	a5,10454 <memset+0x8a>
   103d8:	e5ad                	bnez	a1,10442 <memset+0x78>
   103da:	ff067693          	andi	a3,a2,-16
   103de:	8a3d                	andi	a2,a2,15
   103e0:	96ba                	add	a3,a3,a4
   103e2:	c30c                	sw	a1,0(a4)
   103e4:	c34c                	sw	a1,4(a4)
   103e6:	c70c                	sw	a1,8(a4)
   103e8:	c74c                	sw	a1,12(a4)
   103ea:	0741                	addi	a4,a4,16
   103ec:	fed76be3          	bltu	a4,a3,103e2 <memset+0x18>
   103f0:	e211                	bnez	a2,103f4 <memset+0x2a>
   103f2:	8082                	ret
   103f4:	40c306b3          	sub	a3,t1,a2
   103f8:	068a                	slli	a3,a3,0x2
   103fa:	00000297          	auipc	t0,0x0
   103fe:	9696                	add	a3,a3,t0
   10400:	00a68067          	jr	10(a3)
   10404:	00b70723          	sb	a1,14(a4)
   10408:	00b706a3          	sb	a1,13(a4)
   1040c:	00b70623          	sb	a1,12(a4)
   10410:	00b705a3          	sb	a1,11(a4)
   10414:	00b70523          	sb	a1,10(a4)
   10418:	00b704a3          	sb	a1,9(a4)
   1041c:	00b70423          	sb	a1,8(a4)
   10420:	00b703a3          	sb	a1,7(a4)
   10424:	00b70323          	sb	a1,6(a4)
   10428:	00b702a3          	sb	a1,5(a4)
   1042c:	00b70223          	sb	a1,4(a4)
   10430:	00b701a3          	sb	a1,3(a4)
   10434:	00b70123          	sb	a1,2(a4)
   10438:	00b700a3          	sb	a1,1(a4)
   1043c:	00b70023          	sb	a1,0(a4)
   10440:	8082                	ret
   10442:	0ff5f593          	andi	a1,a1,255
   10446:	00859693          	slli	a3,a1,0x8
   1044a:	8dd5                	or	a1,a1,a3
   1044c:	01059693          	slli	a3,a1,0x10
   10450:	8dd5                	or	a1,a1,a3
   10452:	b761                	j	103da <memset+0x10>
   10454:	00279693          	slli	a3,a5,0x2
   10458:	00000297          	auipc	t0,0x0
   1045c:	9696                	add	a3,a3,t0
   1045e:	8286                	mv	t0,ra
   10460:	fa8680e7          	jalr	-88(a3)
   10464:	8096                	mv	ra,t0
   10466:	17c1                	addi	a5,a5,-16
   10468:	8f1d                	sub	a4,a4,a5
   1046a:	963e                	add	a2,a2,a5
   1046c:	f8c374e3          	bgeu	t1,a2,103f4 <memset+0x2a>
   10470:	b7a5                	j	103d8 <memset+0xe>

00010472 <__call_exitprocs>:
   10472:	7179                	addi	sp,sp,-48
   10474:	cc52                	sw	s4,24(sp)
   10476:	0a81aa03          	lw	s4,168(gp) # 11ec0 <_global_impure_ptr>
   1047a:	d04a                	sw	s2,32(sp)
   1047c:	148a2903          	lw	s2,328(s4)
   10480:	d606                	sw	ra,44(sp)
   10482:	d422                	sw	s0,40(sp)
   10484:	d226                	sw	s1,36(sp)
   10486:	ce4e                	sw	s3,28(sp)
   10488:	ca56                	sw	s5,20(sp)
   1048a:	c85a                	sw	s6,16(sp)
   1048c:	c65e                	sw	s7,12(sp)
   1048e:	c462                	sw	s8,8(sp)
   10490:	02090863          	beqz	s2,104c0 <__call_exitprocs+0x4e>
   10494:	8b2a                	mv	s6,a0
   10496:	8bae                	mv	s7,a1
   10498:	4a85                	li	s5,1
   1049a:	59fd                	li	s3,-1
   1049c:	00492483          	lw	s1,4(s2)
   104a0:	fff48413          	addi	s0,s1,-1
   104a4:	00044e63          	bltz	s0,104c0 <__call_exitprocs+0x4e>
   104a8:	048a                	slli	s1,s1,0x2
   104aa:	94ca                	add	s1,s1,s2
   104ac:	020b8663          	beqz	s7,104d8 <__call_exitprocs+0x66>
   104b0:	1044a783          	lw	a5,260(s1)
   104b4:	03778263          	beq	a5,s7,104d8 <__call_exitprocs+0x66>
   104b8:	147d                	addi	s0,s0,-1
   104ba:	14f1                	addi	s1,s1,-4
   104bc:	ff3418e3          	bne	s0,s3,104ac <__call_exitprocs+0x3a>
   104c0:	50b2                	lw	ra,44(sp)
   104c2:	5422                	lw	s0,40(sp)
   104c4:	5492                	lw	s1,36(sp)
   104c6:	5902                	lw	s2,32(sp)
   104c8:	49f2                	lw	s3,28(sp)
   104ca:	4a62                	lw	s4,24(sp)
   104cc:	4ad2                	lw	s5,20(sp)
   104ce:	4b42                	lw	s6,16(sp)
   104d0:	4bb2                	lw	s7,12(sp)
   104d2:	4c22                	lw	s8,8(sp)
   104d4:	6145                	addi	sp,sp,48
   104d6:	8082                	ret
   104d8:	00492783          	lw	a5,4(s2)
   104dc:	40d4                	lw	a3,4(s1)
   104de:	17fd                	addi	a5,a5,-1
   104e0:	04878263          	beq	a5,s0,10524 <__call_exitprocs+0xb2>
   104e4:	0004a223          	sw	zero,4(s1)
   104e8:	dae1                	beqz	a3,104b8 <__call_exitprocs+0x46>
   104ea:	18892783          	lw	a5,392(s2)
   104ee:	008a9733          	sll	a4,s5,s0
   104f2:	00492c03          	lw	s8,4(s2)
   104f6:	8ff9                	and	a5,a5,a4
   104f8:	ef89                	bnez	a5,10512 <__call_exitprocs+0xa0>
   104fa:	9682                	jalr	a3
   104fc:	00492703          	lw	a4,4(s2)
   10500:	148a2783          	lw	a5,328(s4)
   10504:	01871463          	bne	a4,s8,1050c <__call_exitprocs+0x9a>
   10508:	fb2788e3          	beq	a5,s2,104b8 <__call_exitprocs+0x46>
   1050c:	dbd5                	beqz	a5,104c0 <__call_exitprocs+0x4e>
   1050e:	893e                	mv	s2,a5
   10510:	b771                	j	1049c <__call_exitprocs+0x2a>
   10512:	18c92783          	lw	a5,396(s2)
   10516:	0844a583          	lw	a1,132(s1)
   1051a:	8f7d                	and	a4,a4,a5
   1051c:	e719                	bnez	a4,1052a <__call_exitprocs+0xb8>
   1051e:	855a                	mv	a0,s6
   10520:	9682                	jalr	a3
   10522:	bfe9                	j	104fc <__call_exitprocs+0x8a>
   10524:	00892223          	sw	s0,4(s2)
   10528:	b7c1                	j	104e8 <__call_exitprocs+0x76>
   1052a:	852e                	mv	a0,a1
   1052c:	9682                	jalr	a3
   1052e:	b7f9                	j	104fc <__call_exitprocs+0x8a>

00010530 <__libc_fini_array>:
   10530:	1141                	addi	sp,sp,-16
   10532:	c422                	sw	s0,8(sp)
   10534:	00001797          	auipc	a5,0x1
   10538:	0e078793          	addi	a5,a5,224 # 11614 <__fini_array_end>
   1053c:	00001417          	auipc	s0,0x1
   10540:	0d440413          	addi	s0,s0,212 # 11610 <__do_global_dtors_aux_fini_array_entry>
   10544:	8f81                	sub	a5,a5,s0
   10546:	c226                	sw	s1,4(sp)
   10548:	c606                	sw	ra,12(sp)
   1054a:	4027d493          	srai	s1,a5,0x2
   1054e:	c881                	beqz	s1,1055e <__libc_fini_array+0x2e>
   10550:	17f1                	addi	a5,a5,-4
   10552:	943e                	add	s0,s0,a5
   10554:	401c                	lw	a5,0(s0)
   10556:	14fd                	addi	s1,s1,-1
   10558:	1471                	addi	s0,s0,-4
   1055a:	9782                	jalr	a5
   1055c:	fce5                	bnez	s1,10554 <__libc_fini_array+0x24>
   1055e:	40b2                	lw	ra,12(sp)
   10560:	4422                	lw	s0,8(sp)
   10562:	4492                	lw	s1,4(sp)
   10564:	0141                	addi	sp,sp,16
   10566:	8082                	ret

00010568 <atexit>:
   10568:	85aa                	mv	a1,a0
   1056a:	4681                	li	a3,0
   1056c:	4601                	li	a2,0
   1056e:	4501                	li	a0,0
   10570:	a009                	j	10572 <__register_exitproc>

00010572 <__register_exitproc>:
   10572:	0a81a703          	lw	a4,168(gp) # 11ec0 <_global_impure_ptr>
   10576:	14872783          	lw	a5,328(a4)
   1057a:	c3a1                	beqz	a5,105ba <__register_exitproc+0x48>
   1057c:	43d8                	lw	a4,4(a5)
   1057e:	487d                	li	a6,31
   10580:	04e84d63          	blt	a6,a4,105da <__register_exitproc+0x68>
   10584:	00271813          	slli	a6,a4,0x2
   10588:	c11d                	beqz	a0,105ae <__register_exitproc+0x3c>
   1058a:	01078333          	add	t1,a5,a6
   1058e:	08c32423          	sw	a2,136(t1) # 101a8 <mula32+0x8>
   10592:	1887a883          	lw	a7,392(a5)
   10596:	4605                	li	a2,1
   10598:	00e61633          	sll	a2,a2,a4
   1059c:	00c8e8b3          	or	a7,a7,a2
   105a0:	1917a423          	sw	a7,392(a5)
   105a4:	10d32423          	sw	a3,264(t1)
   105a8:	4689                	li	a3,2
   105aa:	00d50d63          	beq	a0,a3,105c4 <__register_exitproc+0x52>
   105ae:	0705                	addi	a4,a4,1
   105b0:	c3d8                	sw	a4,4(a5)
   105b2:	97c2                	add	a5,a5,a6
   105b4:	c78c                	sw	a1,8(a5)
   105b6:	4501                	li	a0,0
   105b8:	8082                	ret
   105ba:	14c70793          	addi	a5,a4,332
   105be:	14f72423          	sw	a5,328(a4)
   105c2:	bf6d                	j	1057c <__register_exitproc+0xa>
   105c4:	18c7a683          	lw	a3,396(a5)
   105c8:	0705                	addi	a4,a4,1
   105ca:	c3d8                	sw	a4,4(a5)
   105cc:	8e55                	or	a2,a2,a3
   105ce:	18c7a623          	sw	a2,396(a5)
   105d2:	97c2                	add	a5,a5,a6
   105d4:	c78c                	sw	a1,8(a5)
   105d6:	4501                	li	a0,0
   105d8:	8082                	ret
   105da:	557d                	li	a0,-1
   105dc:	8082                	ret

000105de <_exit>:
   105de:	05d00893          	li	a7,93
   105e2:	00000073          	ecall
   105e6:	00054363          	bltz	a0,105ec <_exit+0xe>
   105ea:	a001                	j	105ea <_exit+0xc>
   105ec:	1141                	addi	sp,sp,-16
   105ee:	c422                	sw	s0,8(sp)
   105f0:	842a                	mv	s0,a0
   105f2:	c606                	sw	ra,12(sp)
   105f4:	40800433          	neg	s0,s0
   105f8:	2019                	jal	105fe <__errno>
   105fa:	c100                	sw	s0,0(a0)
   105fc:	a001                	j	105fc <_exit+0x1e>

000105fe <__errno>:
   105fe:	0b41a503          	lw	a0,180(gp) # 11ecc <_impure_ptr>
   10602:	8082                	ret
