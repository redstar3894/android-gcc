/* License terms see GNU GENERAL PUBLIC LICENSE Version 3.
 * Version 20100527.1
 * Magnus Granberg (Zorry) <zorry@gentoo.org>  */
#ifndef GCC_ESP_H
#define GCC_ESP_H

/*	This file will add -fstack-protector-all, -fPIE, -pie and -z now 
	as default if the defines and the spec allow it.
	Added a hack for gcc-specs-* in toolchain-funcs.eclass and _filter-hardened in flag-o-matic.eclass
	to support older hardened GCC patches and we don't need to change the code on gcc-specs-* and _filter-hardened.
	This will add some unsupported upstream commands options as -nopie and -nonow.
	-D__KERNEL__ is added so we don't have -fPIE, -pie and -fstack-protector-all when building kernels.
	ESP_CC1_SPEC is added to CC1_SPEC.
	ESP_CC1_STRICT_OVERFLOW_SPEC is added so we don't disable the strict-overflow check.
	ESP_LINK_PIE_CHECK_SPEC check for -pie, -p, -pg, -profile and -static.
	ENABLE_CRTBEGINTS add support for crtbeginTS.o, build -static with -fPIE or -fpie.
*/
#ifdef ENABLE_ESP
	
	/* Hack to support gcc-specs-* in toolchain-funcs.eclass and _filter-hardened in flag-o-matic.eclass  */
	#define ESP_CC1_SPEC " %(esp_cc1_ssp) %(esp_cc1_pie) %(esp_cc1_strict_overflow)"
	#if defined ( EFAULT_SSP ) || defined ( EFAULT_PIE_SSP )
		#define ESP_CC1_SSP_SPEC "%{!fno-stack-protector: %{!fno-stack-protector-all: }}"
	#else
		#define ESP_CC1_SSP_SPEC ""
	#endif
	#if defined ( EFAULT_PIE ) || defined ( EFAULT_PIE_SSP )
		#define ESP_CC1_PIE_SPEC "%{!nopie: }"
	#else
		#define ESP_CC1_PIE_SPEC ""
	#endif
	#define ESP_CC1_STRICT_OVERFLOW_SPEC "%{!fstrict-overflow:%{!fno-strict-overflow: -fno-strict-overflow}}"

	/*	ESP_LINK_SPEC is added to LINK_PIE_SPEC if esp is enable
		-z now will be added if we don't have -vanilla spec. We do a -pie incompatible check
		Don't remove the specs in the end  */
	#define ESP_LINK_SPEC "%(esp_link_now) %(esp_link_pie_check) "
	#define ESP_LINK_NOW_SPEC "%{!nonow:-z now}"

	/*	We use ESP_COMMAND_OPTIONS_SPEC to add pie command-line options.  */
	#define ESP_COMMAND_OPTIONS_SPEC "%{!D__KERNEL__:%{!nopie:%(esp_options_pie) %(esp_link_pie)}}"
	
	/*	ESP_OPTIONS_SPEC is added to the compiler spec in gcc/gcc.c  */
	#define ESP_OPTIONS_SPEC "%(esp_options_ssp)"

	/*	ESP_CPP_OPTIONS_SPEC is added to the cpp_options spec in gcc/gcc.c  
		For precompiling headers.  */
	#define ESP_CPP_OPTIONS_SPEC "%(esp_options_ssp)"

	/*  This will add -fstack-protector-all if we don't have -nostdlib -nodefaultlibs -fno-stack-protector -fstack-protector
		-fstack-protector-all and we have EFAULT_SSP or EFAULT_PIE_SSP defined.  */
	#if defined ( EFAULT_SSP ) || defined ( EFAULT_PIE_SSP )
		#define ESP_OPTIONS_SSP_SPEC \
			"%{!D__KERNEL__:%{!nostdlib:%{!nodefaultlibs: %{!fno-stack-protector: \
			%{!fstack-protector:%{!fstack-protector-all:-fstack-protector-all}}}}}}"
	#else
		#define ESP_OPTIONS_SSP_SPEC ""
	#endif

	/* If EFAULT_PIE or EFAULT_PIE_SSP is defined we will add -fPIE -pie  */
	#if defined ( EFAULT_PIE ) || defined ( EFAULT_PIE_SSP )

		/*  This will add -fPIE if we don't have -pie -fpic -fPIC -fpie -fPIE -fno-pic -fno-PIC -fno-pie -fno-PIE -shared -static
			-nostdlib -nostartfiles.  */
		/*  With ENABLE_CRTBEGINTS we don't need to check for -static  */
		#ifdef ENABLE_CRTBEGINTS
			#define ESP_OPTIONS_PIE_SPEC \
				"%{!pie: %{!fpic:%{!fPIC:%{!fpie:%{!fPIE: %{!fno-pic:%{!fno-PIC:%{!fno-pie:%{!fno-PIE: \
				%{!shared: %{!nostdlib: %{!nostartfiles:-fPIE}} } }}}} }}}} }"
		#else
			#define ESP_OPTIONS_PIE_SPEC \
				"%{!pie: %{!fpic:%{!fPIC:%{!fpie:%{!fPIE: %{!fno-pic:%{!fno-PIC:%{!fno-pie:%{!fno-PIE: \
				%{!shared: %{!static: %{!nostdlib: %{!nostartfiles:-fPIE}} } }}}} }}}} }}"
		#endif

		/*  This will add -pie if we don't have -pie -A -fno-pic -fno-PIC -fno-pie -fno-PIE -shared -static -r -nostdlib 
			-nostartfiles  */
		/*  With ENABLE_CRTBEGINTS we don't need to check for -static
			and we add -pie only to get the start and endfiles. -pie will not go to the linker. */
		#ifdef ENABLE_CRTBEGINTS
			#define ESP_LINK_PIE_SPEC \
				"%{!pie:%{!A:%{!fno-pie:%{!fno-PIE:%{!fno-pic:%{!fno-PIC:%{!shared:%{!r: \
				%{!nostdlib:%{!nostartfiles:-pie}}}}}}}}}}"
		#else
			#define ESP_LINK_PIE_SPEC \
				"%{!pie:%{!A:%{!fno-pie:%{!fno-PIE:%{!fno-pic:%{!fno-PIC:%{!shared:%{!static:%{!r: \
				%{!nostdlib:%{!nostartfiles:-pie}}}}}}}}}}}"
		#endif
		
		/*  This will check if -pie is set when (-static) -pg -p -profile. If set it will make gcc print out
			"-pie and (static)|pg|p|profile are incompatible when linking"  */
		/*  With ENABLE_CRTBEGINTS we don't need to check for -static  */
		#ifdef ENABLE_CRTBEGINTS
			#define ESP_LINK_PIE_CHECK_SPEC \
				"%{pie:%{pg|p|profile:%e-pie and -pg|p|profile are incompatible when linking}}"
		#else
			#define ESP_LINK_PIE_CHECK_SPEC \
				"%{pie:%{static|pg|p|profile:%e-pie and -static|pg|p|profile are incompatible when linking}}"
		#endif

		/*  We don't pass -pie to the linker when -static.  */
		#ifdef ENABLE_CRTBEGINTS
			#define LINK_PIE_SPEC "%{!static:%{pie:-pie}} %(esp_link)"
		#else
			#define LINK_PIE_SPEC "%{pie:-pie} %(esp_link)"
		#endif

	#else
		#define ESP_OPTIONS_PIE_SPEC ""
		#define ESP_LINK_PIE_CHECK_SPEC ""
		#define ESP_LINK_PIE_SPEC ""
		#define LINK_PIE_SPEC "%{pie:-pie} %(esp_link)"
	#endif

	/*  We add extra spec name's to the EXTRA_SPECS list  */
	#define ESP_EXTRA_SPECS \
		{ "esp_cc1",								ESP_CC1_SPEC },					\
		{ "esp_cc1_pie",							ESP_CC1_PIE_SPEC },				\
		{ "esp_cc1_ssp",							ESP_CC1_SSP_SPEC },				\
		{ "esp_cc1_strict_overflow",				ESP_CC1_STRICT_OVERFLOW_SPEC },	\
		{ "esp_link",								ESP_LINK_SPEC },				\
		{ "esp_link_now",							ESP_LINK_NOW_SPEC },			\
		{ "esp_link_pie",							ESP_LINK_PIE_SPEC },			\
		{ "esp_link_pie_check",						ESP_LINK_PIE_CHECK_SPEC },		\
		{ "esp_command_options",					ESP_COMMAND_OPTIONS_SPEC },		\
		{ "esp_cpp_options",						ESP_CPP_OPTIONS_SPEC },			\
		{ "esp_options",							ESP_OPTIONS_SPEC },				\
		{ "esp_options_pie",						ESP_OPTIONS_PIE_SPEC },			\
		{ "esp_options_ssp",						ESP_OPTIONS_SSP_SPEC }

	static const char *esp_command_options_spec = ESP_COMMAND_OPTIONS_SPEC;
	static const char *cc1_spec = CC1_SPEC ESP_CC1_SPEC;

#else /* If not ESP_ENABLE defined do this.  */

	#define ESP_OPTIONS_SPEC ""
	#define ESP_CPP_OPTIONS_SPEC ""

	/*  We add extra spec name's to the EXTRA_SPECS list  */
	#define ESP_EXTRA_SPECS \
		{ "esp_options",				ESP_OPTIONS_SPEC },			\
		{ "esp_cpp_options",			ESP_CPP_OPTIONS_SPEC }

#endif
#endif /* End GCC_ESP_H */
