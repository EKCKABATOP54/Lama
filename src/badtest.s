	.file "/home/androposh/Projects/Lama/src/badtest.lama"

	.stabs "/home/androposh/Projects/Lama/src/badtest.lama",100,0,0,.Ltext

	.globl	main
	.globl	main_type

	.data

_init:	.int 0

	.section custom_data,"aw",@progbits

filler:	.fill	8, 4, 1

	.stabs "c:S1",40,0,0,global_c

global_c:	.int	1

	.stabs "c_type:S1",40,0,0,global_c_type

global_c_type:	.int	1

	.stabs "d:S1",40,0,0,global_d

global_d:	.int	1

	.stabs "d_type:S1",40,0,0,global_d_type

global_d_type:	.int	1

	.stabs "i:S1",40,0,0,global_i

global_i:	.int	1

	.stabs "i_type:S1",40,0,0,global_i_type

global_i_type:	.int	1

	.stabs "m:S1",40,0,0,global_m

global_m:	.int	1

	.stabs "m_type:S1",40,0,0,global_m_type

global_m_type:	.int	1

	.stabs "n:S1",40,0,0,global_n

global_n:	.int	1

	.stabs "n_type:S1",40,0,0,global_n_type

global_n_type:	.int	1

	.stabs "p:S1",40,0,0,global_p

global_p:	.int	1

	.stabs "p_type:S1",40,0,0,global_p_type

global_p_type:	.int	1

	.stabs "q:S1",40,0,0,global_q

global_q:	.int	1

	.stabs "q_type:S1",40,0,0,global_q_type

global_q_type:	.int	1

	.text

.Ltext:

	.stabs "data:t1=r1;0;4294967295;",128,0,0,0

# IMPORT ("Std") / 

# PUBLIC ("main") / 

# EXTERN ("Llowercase") / 

# EXTERN ("Luppercase") / 

# EXTERN ("LtagHash") / 

# EXTERN ("LflatCompare") / 

# EXTERN ("LcompareTags") / 

# EXTERN ("LkindOf") / 

# EXTERN ("Ltime") / 

# EXTERN ("Lrandom") / 

# EXTERN ("LdisableGC") / 

# EXTERN ("LenableGC") / 

# EXTERN ("Ls__Infix_37") / 

# EXTERN ("Ls__Infix_47") / 

# EXTERN ("Ls__Infix_42") / 

# EXTERN ("Ls__Infix_45") / 

# EXTERN ("Ls__Infix_43") / 

# EXTERN ("Ls__Infix_62") / 

# EXTERN ("Ls__Infix_6261") / 

# EXTERN ("Ls__Infix_60") / 

# EXTERN ("Ls__Infix_6061") / 

# EXTERN ("Ls__Infix_3361") / 

# EXTERN ("Ls__Infix_6161") / 

# EXTERN ("Ls__Infix_3838") / 

# EXTERN ("Ls__Infix_3333") / 

# EXTERN ("Ls__Infix_58") / 

# EXTERN ("Li__Infix_4343") / 

# EXTERN ("Lcompare") / 

# EXTERN ("Lwrite") / 

# EXTERN ("Lread") / 

# EXTERN ("Lfailure") / 

# EXTERN ("Lfexists") / 

# EXTERN ("Lfwrite") / 

# EXTERN ("Lfread") / 

# EXTERN ("Lfclose") / 

# EXTERN ("Lfopen") / 

# EXTERN ("Lfprintf") / 

# EXTERN ("Lprintf") / 

# EXTERN ("LmakeString") / 

# EXTERN ("Lsprintf") / 

# EXTERN ("LregexpMatch") / 

# EXTERN ("Lregexp") / 

# EXTERN ("Lsubstring") / 

# EXTERN ("LmatchSubString") / 

# EXTERN ("Lstringcat") / 

# EXTERN ("LreadLine") / 

# EXTERN ("Ltl") / 

# EXTERN ("Lhd") / 

# EXTERN ("Lsnd") / 

# EXTERN ("Lfst") / 

# EXTERN ("Lhash") / 

# EXTERN ("Lclone") / 

# EXTERN ("Llength") / 

# EXTERN ("Lstring") / 

# EXTERN ("LmakeArray") / 

# EXTERN ("LstringInt") / 

# EXTERN ("global_stderr") / 

# EXTERN ("global_stdout") / 

# EXTERN ("global_sysargs") / 

# EXTERN ("Lsystem") / 

# EXTERN ("LgetEnv") / 

# EXTERN ("Lassert") / 

# LABEL ("main") / 

main:

# BEGIN ("main", 2, 1, [], [], []) / 

	.type main, @function

	.cfi_startproc

	movl	_init,	%eax
	test	%eax,	%eax
	jz	_continue
	ret
_ERROR:

	call	Lbinoperror
	ret
_ERROR2:

	call	Lbinoperror2
	ret
_continue:

	movl	$1,	_init
	pushl	%ebp
	.cfi_def_cfa_offset	8

	.cfi_offset 5, -8

	movl	%esp,	%ebp
	.cfi_def_cfa_register	5

	subl	$Lmain_SIZE,	%esp
	movl	%esp,	%edi
	movl	$filler,	%esi
	movl	$LSmain_SIZE,	%ecx
	rep movsl	
	call	__gc_init
	pushl	12(%ebp)
	pushl	8(%ebp)
	call	set_args
	addl	$8,	%esp
# SLABEL ("L1") / 

L1:

# LINE (3) / 

	.stabn 68,0,3,.L0

.L0:

# CALL ("Lread", 0, false) / 

	call	Lread
	addl	$0,	%esp
	movl	4(%eax),	%ebx
	movl	%ebx,	-16(%ebp)
	movl	(%eax),	%ebx
	movl	%ebx,	-12(%ebp)
# LINE (1) / 

	.stabn 68,0,1,.L1

.L1:

# ST (Global ("n")) / 

	movl	-16(%ebp),	%eax
	movl	%eax,	global_n
	movl	-12(%ebp),	%eax
	movl	%eax,	global_n_type
# DROP / 

# CONST (1) / 

	movl	$222,	-12(%ebp)
	movl	$3,	-16(%ebp)
# ST (Global ("c")) / 

	movl	-16(%ebp),	%eax
	movl	%eax,	global_c
	movl	-12(%ebp),	%eax
	movl	%eax,	global_c_type
# DROP / 

# CONST (2) / 

	movl	$222,	-12(%ebp)
	movl	$5,	-16(%ebp)
# LINE (5) / 

	.stabn 68,0,5,.L2

.L2:

# ST (Global ("p")) / 

	movl	-16(%ebp),	%eax
	movl	%eax,	global_p
	movl	-12(%ebp),	%eax
	movl	%eax,	global_p_type
# DROP / 

# JMP ("L16") / 

	jmp	L16
# FLABEL ("L15") / 

L15:

# SLABEL ("L17") / 

L17:

# CONST (1) / 

	movl	$222,	-12(%ebp)
	movl	$3,	-16(%ebp)
# LINE (10) / 

	.stabn 68,0,10,.L3

.L3:

# ST (Local (0)) / 

	movl	-16(%ebp),	%eax
	movl	%eax,	-8(%ebp)
	movl	-12(%ebp),	%eax
	movl	%eax,	-4(%ebp)
# DROP / 

# JMP ("L25") / 

	jmp	L25
# FLABEL ("L24") / 

L24:

# SLABEL ("L26") / 

L26:

# CONST (2) / 

	movl	$222,	-12(%ebp)
	movl	$5,	-16(%ebp)
# ST (Global ("q")) / 

	movl	-16(%ebp),	%eax
	movl	%eax,	global_q
	movl	-12(%ebp),	%eax
	movl	%eax,	global_q_type
# DROP / 

# LINE (14) / 

	.stabn 68,0,14,.L4

.L4:

# LD (Local (0)) / 

	movl	-8(%ebp),	%eax
	movl	%eax,	-16(%ebp)
	movl	-4(%ebp),	%eax
	movl	%eax,	-12(%ebp)
# CJMP ("z", "L32") / 

	sarl	-16(%ebp)
	cmpl	$0,	-16(%ebp)
	jz	L32
# SLABEL ("L33") / 

L33:

# CONST (0) / 

	movl	$222,	-12(%ebp)
	movl	$1,	-16(%ebp)
# ST (Local (0)) / 

	movl	-16(%ebp),	%eax
	movl	%eax,	-8(%ebp)
	movl	-12(%ebp),	%eax
	movl	%eax,	-4(%ebp)
# DROP / 

# SLABEL ("L34") / 

L34:

# JMP ("L25") / 

	jmp	L25
# LABEL ("L32") / 

L32:

# SLABEL ("L37") / 

L37:

# LD (Global ("p")) / 

	movl	global_p,	%eax
	movl	%eax,	-16(%ebp)
	movl	global_p_type,	%eax
	movl	%eax,	-12(%ebp)
# CONST (1) / 

	movl	$222,	-20(%ebp)
	movl	$3,	-24(%ebp)
# BINOP ("+") / 

	movl	-24(%ebp),	%eax
	decl	%eax
	addl	%eax,	-16(%ebp)
# ST (Global ("p")) / 

	movl	-16(%ebp),	%eax
	movl	%eax,	global_p
	movl	-12(%ebp),	%eax
	movl	%eax,	global_p_type
# DROP / 

# CONST (1) / 

	movl	$222,	-12(%ebp)
	movl	$3,	-16(%ebp)
# ST (Local (0)) / 

	movl	-16(%ebp),	%eax
	movl	%eax,	-8(%ebp)
	movl	-12(%ebp),	%eax
	movl	%eax,	-4(%ebp)
# DROP / 

# SLABEL ("L38") / 

L38:

# JMP ("L25") / 

	jmp	L25
# SLABEL ("L27") / 

L27:

# LABEL ("L25") / 

L25:

# LINE (12) / 

	.stabn 68,0,12,.L5

.L5:

# LD (Local (0)) / 

	movl	-8(%ebp),	%eax
	movl	%eax,	-16(%ebp)
	movl	-4(%ebp),	%eax
	movl	%eax,	-12(%ebp)
# CJMP ("nz", "L24") / 

	sarl	-16(%ebp)
	cmpl	$0,	-16(%ebp)
	jnz	L24
# LINE (17) / 

	.stabn 68,0,17,.L6

.L6:

# LD (Global ("p")) / 

	movl	global_p,	%eax
	movl	%eax,	-16(%ebp)
	movl	global_p_type,	%eax
	movl	%eax,	-12(%ebp)
# LINE (15) / 

	.stabn 68,0,15,.L7

.L7:

# ST (Global ("d")) / 

	movl	-16(%ebp),	%eax
	movl	%eax,	global_d
	movl	-12(%ebp),	%eax
	movl	%eax,	global_d_type
# DROP / 

# CONST (0) / 

	movl	$222,	-12(%ebp)
	movl	$1,	-16(%ebp)
# ST (Global ("i")) / 

	movl	-16(%ebp),	%eax
	movl	%eax,	global_i
	movl	-12(%ebp),	%eax
	movl	%eax,	global_i_type
# DROP / 

# LINE (20) / 

	.stabn 68,0,20,.L8

.L8:

# LD (Global ("n")) / 

	movl	global_n,	%eax
	movl	%eax,	-16(%ebp)
	movl	global_n_type,	%eax
	movl	%eax,	-12(%ebp)
# LD (Global ("d")) / 

	movl	global_d,	%eax
	movl	%eax,	-24(%ebp)
	movl	global_d_type,	%eax
	movl	%eax,	-20(%ebp)
# BINOP ("/") / 

	movl	-16(%ebp),	%eax
	sarl	%eax
	cltd
	sarl	-24(%ebp)
	idivl	-24(%ebp)
	sall	%eax
	orl	$0x0001,	%eax
	movl	%eax,	-16(%ebp)
# LINE (18) / 

	.stabn 68,0,18,.L9

.L9:

# ST (Global ("q")) / 

	movl	-16(%ebp),	%eax
	movl	%eax,	global_q
	movl	-12(%ebp),	%eax
	movl	%eax,	global_q_type
# DROP / 

# LINE (21) / 

	.stabn 68,0,21,.L10

.L10:

# LD (Global ("n")) / 

	movl	global_n,	%eax
	movl	%eax,	-16(%ebp)
	movl	global_n_type,	%eax
	movl	%eax,	-12(%ebp)
# LD (Global ("d")) / 

	movl	global_d,	%eax
	movl	%eax,	-24(%ebp)
	movl	global_d_type,	%eax
	movl	%eax,	-20(%ebp)
# BINOP ("%") / 

	movl	-16(%ebp),	%eax
	sarl	%eax
	cltd
	sarl	-24(%ebp)
	idivl	-24(%ebp)
	sall	%edx
	orl	$0x0001,	%edx
	movl	%edx,	-16(%ebp)
# ST (Global ("m")) / 

	movl	-16(%ebp),	%eax
	movl	%eax,	global_m
	movl	-12(%ebp),	%eax
	movl	%eax,	global_m_type
# DROP / 

# JMP ("L65") / 

	jmp	L65
# FLABEL ("L64") / 

L64:

# SLABEL ("L72") / 

L72:

# LINE (24) / 

	.stabn 68,0,24,.L11

.L11:

# LD (Global ("i")) / 

	movl	global_i,	%eax
	movl	%eax,	-16(%ebp)
	movl	global_i_type,	%eax
	movl	%eax,	-12(%ebp)
# CONST (1) / 

	movl	$222,	-20(%ebp)
	movl	$3,	-24(%ebp)
# BINOP ("+") / 

	movl	-24(%ebp),	%eax
	decl	%eax
	addl	%eax,	-16(%ebp)
# ST (Global ("i")) / 

	movl	-16(%ebp),	%eax
	movl	%eax,	global_i
	movl	-12(%ebp),	%eax
	movl	%eax,	global_i_type
# DROP / 

# LINE (25) / 

	.stabn 68,0,25,.L12

.L12:

# LD (Global ("d")) / 

	movl	global_d,	%eax
	movl	%eax,	-16(%ebp)
	movl	global_d_type,	%eax
	movl	%eax,	-12(%ebp)
# LD (Global ("p")) / 

	movl	global_p,	%eax
	movl	%eax,	-24(%ebp)
	movl	global_p_type,	%eax
	movl	%eax,	-20(%ebp)
# BINOP ("*") / 

	decl	-16(%ebp)
	movl	-24(%ebp),	%eax
	sarl	%eax
	imull	-16(%ebp),	%eax
	orl	$0x0001,	%eax
	movl	%eax,	-16(%ebp)
# ST (Global ("d")) / 

	movl	-16(%ebp),	%eax
	movl	%eax,	global_d
	movl	-12(%ebp),	%eax
	movl	%eax,	global_d_type
# DROP / 

# LINE (26) / 

	.stabn 68,0,26,.L13

.L13:

# LD (Global ("m")) / 

	movl	global_m,	%eax
	movl	%eax,	-16(%ebp)
	movl	global_m_type,	%eax
	movl	%eax,	-12(%ebp)
# CONST (0) / 

	movl	$222,	-20(%ebp)
	movl	$1,	-24(%ebp)
# BINOP ("==") / 

	xorl	%eax,	%eax
	movl	-24(%ebp),	%edx
	cmpl	%edx,	-16(%ebp)
	sete	%al
	sall	%eax
	orl	$0x0001,	%eax
	movl	%eax,	-16(%ebp)
# CJMP ("z", "L85") / 

	sarl	-16(%ebp)
	cmpl	$0,	-16(%ebp)
	jz	L85
# SLABEL ("L88") / 

L88:

# LD (Global ("n")) / 

	movl	global_n,	%eax
	movl	%eax,	-16(%ebp)
	movl	global_n_type,	%eax
	movl	%eax,	-12(%ebp)
# LD (Global ("d")) / 

	movl	global_d,	%eax
	movl	%eax,	-24(%ebp)
	movl	global_d_type,	%eax
	movl	%eax,	-20(%ebp)
# BINOP ("/") / 

	movl	-16(%ebp),	%eax
	sarl	%eax
	cltd
	sarl	-24(%ebp)
	idivl	-24(%ebp)
	sall	%eax
	orl	$0x0001,	%eax
	movl	%eax,	-16(%ebp)
# ST (Global ("q")) / 

	movl	-16(%ebp),	%eax
	movl	%eax,	global_q
	movl	-12(%ebp),	%eax
	movl	%eax,	global_q_type
# DROP / 

# SLABEL ("L89") / 

L89:

# JMP ("L65") / 

	jmp	L65
# LABEL ("L85") / 

L85:

# SLABEL ("L94") / 

L94:

# SLABEL ("L95") / 

L95:

# JMP ("L65") / 

	jmp	L65
# SLABEL ("L73") / 

L73:

# LABEL ("L65") / 

L65:

# LINE (23) / 

	.stabn 68,0,23,.L14

.L14:

# LD (Global ("q")) / 

	movl	global_q,	%eax
	movl	%eax,	-16(%ebp)
	movl	global_q_type,	%eax
	movl	%eax,	-12(%ebp)
# CONST (0) / 

	movl	$222,	-20(%ebp)
	movl	$1,	-24(%ebp)
# BINOP (">") / 

	xorl	%eax,	%eax
	movl	-24(%ebp),	%edx
	cmpl	%edx,	-16(%ebp)
	setg	%al
	sall	%eax
	orl	$0x0001,	%eax
	movl	%eax,	-16(%ebp)
# LD (Global ("m")) / 

	movl	global_m,	%eax
	movl	%eax,	-24(%ebp)
	movl	global_m_type,	%eax
	movl	%eax,	-20(%ebp)
# CONST (0) / 

	movl	$222,	-28(%ebp)
	movl	$1,	-32(%ebp)
# BINOP ("==") / 

	xorl	%eax,	%eax
	movl	-32(%ebp),	%edx
	cmpl	%edx,	-24(%ebp)
	sete	%al
	sall	%eax
	orl	$0x0001,	%eax
	movl	%eax,	-24(%ebp)
# BINOP ("&&") / 

	decl	-24(%ebp)
	movl	-24(%ebp),	%eax
	andl	-24(%ebp),	%eax
	movl	$0,	%eax
	setne	%al
	decl	-16(%ebp)
	movl	-16(%ebp),	%edx
	andl	-16(%ebp),	%edx
	movl	$0,	%edx
	setne	%dl
	andl	%edx,	%eax
	setne	%al
	sall	%eax
	orl	$0x0001,	%eax
	movl	%eax,	-16(%ebp)
# CJMP ("nz", "L64") / 

	sarl	-16(%ebp)
	cmpl	$0,	-16(%ebp)
	jnz	L64
# LINE (29) / 

	.stabn 68,0,29,.L15

.L15:

# LD (Global ("p")) / 

	movl	global_p,	%eax
	movl	%eax,	-16(%ebp)
	movl	global_p_type,	%eax
	movl	%eax,	-12(%ebp)
# CONST (1) / 

	movl	$222,	-20(%ebp)
	movl	$3,	-24(%ebp)
# BINOP ("+") / 

	movl	-24(%ebp),	%eax
	decl	%eax
	addl	%eax,	-16(%ebp)
# LINE (27) / 

	.stabn 68,0,27,.L16

.L16:

# ST (Global ("p")) / 

	movl	-16(%ebp),	%eax
	movl	%eax,	global_p
	movl	-12(%ebp),	%eax
	movl	%eax,	global_p_type
# DROP / 

# LINE (30) / 

	.stabn 68,0,30,.L17

.L17:

# LD (Global ("n")) / 

	movl	global_n,	%eax
	movl	%eax,	-16(%ebp)
	movl	global_n_type,	%eax
	movl	%eax,	-12(%ebp)
# CONST (1) / 

	movl	$222,	-20(%ebp)
	movl	$3,	-24(%ebp)
# BINOP ("!=") / 

	xorl	%eax,	%eax
	movl	-24(%ebp),	%edx
	cmpl	%edx,	-16(%ebp)
	setne	%al
	sall	%eax
	orl	$0x0001,	%eax
	movl	%eax,	-16(%ebp)
# ST (Global ("c")) / 

	movl	-16(%ebp),	%eax
	movl	%eax,	global_c
	movl	-12(%ebp),	%eax
	movl	%eax,	global_c_type
# DROP / 

# SLABEL ("L18") / 

L18:

# LABEL ("L16") / 

L16:

# LINE (8) / 

	.stabn 68,0,8,.L18

.L18:

# LD (Global ("c")) / 

	movl	global_c,	%eax
	movl	%eax,	-16(%ebp)
	movl	global_c_type,	%eax
	movl	%eax,	-12(%ebp)
# CJMP ("nz", "L15") / 

	sarl	-16(%ebp)
	cmpl	$0,	-16(%ebp)
	jnz	L15
# CONST (0) / 

	movl	$222,	-12(%ebp)
	movl	$1,	-16(%ebp)
# SLABEL ("L2") / 

L2:

# END / 

	call	default_return_memory_loc
	movl	-16(%ebp),	%ebx
	movl	%ebx,	4(%eax)
	movl	-12(%ebp),	%ebx
	movl	%ebx,	(%eax)
Lmain_epilogue:

	movl	%ebp,	%esp
	popl	%ebp
	xorl	%eax,	%eax
	.cfi_restore	5

	.cfi_def_cfa	4, 4

	ret
	.cfi_endproc

	.set	Lmain_SIZE,	32

	.set	LSmain_SIZE,	8

	.size main, .-main

