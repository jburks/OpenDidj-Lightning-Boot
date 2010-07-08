/* main.c -- Lightning Platform Bootloader
 *
 * Originally Copyright 2007 LeapFrog Enterprises Inc.
 * OpenDidj extensions Copyright 2010 Joe Burks
 *
 * Andrey Yurovsky <andrey@cozybit.com>
 * Joe Burks <joe@burks-family.us>
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License version 2 as
 * published by the Free Software Foundation.
 */

#include "include/autoconf.h"	/* for partition info */
#include "include/mach-types.h" /* for machine info */

#include <platform.h>
#include <common.h>
#include <uart.h>
#include <nand.h>
#include <gpio.h>
#include <gpio_hal.h>
#include <clkpwr.h>
#include <stdint.h>
#include <adc.h>

#include "include/board.h"
#include "include/string.h"
#include "include/setup.h"
#include "include/image.h"
#include "include/debug.h"
#include "include/nand.h"
#include "include/jffs2.h"
#include "include/tfs.h"
#include "include/crc32.h"
#include "include/display.h"
#include "include/clock.h"
#include "include/gpio.h"
#include "include/adc.h"
#include "include/timer.h"
#include "include/xmodem/xmodem.h"
#include "include/fbuffer.h"
#include "include/pff.h"
#include "include/mlc.h"

union errorCode {
	struct {
		u32 code;
	} fullcode ;
	struct {
		u16 upper;
		u16 lower;
	} halfcode;
};

// For switch baud rate of UART
#define UART16(r)       REG16(LF1000_SYS_UART_BASE+r)

/* buffers */
#define FS_BUFFER_SIZE	BOOT_SIZE
static u32 fs_buffer[FS_BUFFER_SIZE/sizeof(u32)];
static u32 sum_buffer[NAND_EB_SIZE/sizeof(u32)];

#define PARAMS_LEN	(1024/4)
static u32 *params_buffer = (u32 *)CONFIG_LF1000_BOOT_PARAMS_ADDR;
static u32 offset = 0;

/* USB controller */
#define UDC_PCR		0x52	/* PCR register offset */
#define PCE		0	/* not-enable bit */

/* network to host, in our case: be32 to le32 */
#define ntohl(x)					\
		((u32)(					\
                (((u32)(x) & (u32)0x000000FFUL)<<24)|	\
                (((u32)(x) & (u32)0x0000FF00UL)<<8) |	\
                (((u32)(x) & (u32)0x00FF0000UL)>>8) |	\
                (((u32)(x) & (u32)0xFF000000UL)>>24)))

void ubcopy (int *data,int size)
{
	if ( (offset & 0xFF) == 0 ) {
		renderHexU32(45,29,(u32)offset);
	}
	
	memcpy ((void *)(UBOOT_ADDR + offset),(void *)data,size);
	
	offset += size;
	return;
}

int __div0(void) { return 0; }

/*
 * Die in case of unrecoverable error.  On LF1000, we pull the power off. 
 * Otherwise just lock up. 
 */
static void die(void)
{
	db_puts("die()\n");
#ifdef CPU_LF1000
	/* enable access to Alive GPIO */
	REG32(LF1000_ALIVE_BASE+ALIVEPWRGATEREG) = 1;
	/* pull VDDPWRON low by resetting the flip-flop */
	BIT_CLR(REG32(LF1000_ALIVE_BASE+ALIVEGPIOSETREG), VDDPWRONSET);
	BIT_SET(REG32(LF1000_ALIVE_BASE+ALIVEGPIORSTREG), VDDPWRONSET);
	/* reset flip-flop to latch in */
	REG32(LF1000_ALIVE_BASE+ALIVEGPIOSETREG) = 0;
	REG32(LF1000_ALIVE_BASE+ALIVEGPIORSTREG) = 0;
	/* power should be off now... */
#endif
	while(1);
}

/*
 * Clean up before booting Linux on the ARM926: turn off instruction cache and 
 * make sure data cache doesn't contain any stale data. 
 */
static void cleanup_for_linux(void)
{
#define C1_DC	(1<<2)	/* dcache off/on */
#define C1_IC	(1<<12)	/* icache off/on */
	unsigned long i;

	/* turn off I/D-cache */
	asm ("mrc p15, 0, %0, c1, c0, 0":"=r" (i));
	i &= ~(C1_DC | C1_IC);
	asm ("mcr p15, 0, %0, c1, c0, 0": :"r" (i));

	/* flush I/D-cache */
	i = 0;
	asm ("mcr p15, 0, %0, c7, c7, 0": :"r" (i));
}

/* 
 * build_params -- set up parameters for the kernel uImage 
 */
static void build_params(char *cmdline, struct tag *params)
{
	char *p;

	/* 
	 * set up the core tag 
	 */
	params->hdr.tag = ATAG_CORE;
	params->hdr.size = tag_size(tag_core);
	params->u.core.flags = 0;
	params->u.core.pagesize = 0;
	params->u.core.rootdev = 0;
	params = tag_next(params);

	/* 
	 * set up the memory tags
	 * Note: there should be one ATAG_MEM per memory bank, we have only one
	 *       bank at this time.
	 */
	params->hdr.tag = ATAG_MEM;
	params->hdr.size = tag_size(tag_mem32);
	params->u.mem.start = SDRAM_START;
	params->u.mem.size = SDRAM_SIZE;
	params = tag_next(params);

	/* 
	 * set up the kernel command line tag 
	 */

	if(cmdline == 0)
		goto END_TAG;
	
	/* eat leading spaces */
	for(p = cmdline; *p == ' '; p++);

	if(*p == '\0')
		goto END_TAG;

	params->hdr.tag = ATAG_CMDLINE;
	params->hdr.size = (sizeof(struct tag_header) + strlen(p) + 1 + 4) >> 2;
	strcpy(params->u.cmdline.cmdline, p);
	params = tag_next(params);

	/*
	 * set up the end tag
	 */
END_TAG:
	params->hdr.tag = ATAG_NONE;
	params->hdr.size = 0;
}

/* 
 * Load kernel image into entry point address.  Assumes that the fs buffer has
 * been filled.
 */
static u32 load_kernel(char *cmdline)
{
	u32 entry_point;
	struct image_header *hdr;

	if(tfs_load_file("uImage", (u32 *)(0x8000-sizeof(image_header_t))) != 0)
		return 0;

	build_params(cmdline, (struct tag *)params_buffer);

	hdr = (struct image_header *)(0x8000-sizeof(image_header_t));
	if(ntohl(hdr->ih_magic) != IH_MAGIC) {
		db_puts("ERROR: bad magic number\n");
		return 0;
	}

#ifdef CHECK_KERNEL_CRC
	do {
		u32 checksum;

		checksum = ntohl(hdr->ih_hcrc);
		hdr->ih_hcrc = 0;

		/* check uImage header CRC */
		if(crc32(0, (u8 *)hdr, sizeof(image_header_t)) != checksum) {
			db_puts("ERROR: header CRC mismatch\n");
		}

		/* check uImage data CRC */
		checksum = crc32(0, (u8 *)hdr+sizeof(image_header_t), 
				ntohl(hdr->ih_size));
		if(checksum != ntohl(hdr->ih_dcrc)) {
			db_puts("ERROR: bad data CRC\n");
			return 0;
		}
	} while(0);
#endif

	entry_point = ntohl(hdr->ih_ep);

	/* Retrieve the kernel image's contents in such a way that the image
	 * header is skipped and the actual start of the kernel sits at the
	 * entry point. */

	return entry_point;
}

#ifdef CPU_LF1000
static int load_board_id(void)
{
	u32 id, scratch;
#if defined CONFIG_MACH_ME_LF1000 || defined CONFIG_MACH_ME_MP2530F
	id = 0;
#else
	int i;

	/* make pins inputs */
	for(i = GPIO_CFG_HIGH; i >= GPIO_CFG_LOW; i--)
		gpio_config_pin(GPIO_CFG_PORT, i, GPIO_GPIOFN, 0, 0, 0);

	/* read pins */
	for(id = 0, i = GPIO_CFG_HIGH; i >= GPIO_CFG_LOW; i--)
		id = (id << 1) + gpio_get_val(GPIO_CFG_PORT, i);
#endif /* CONFIG_MACH_LF_LF1000 */

	/* save into scratchpad register */
	scratch = gpio_get_scratchpad();
	scratch &= ~(BIT_MASK(GPIO_CFG_HIGH-GPIO_CFG_LOW+1) <<
			SCRATCH_BOARD_ID_POS);
	scratch |= (id<<SCRATCH_BOARD_ID_POS);
	gpio_set_scratchpad(scratch);
	return id;
}	

static int sd_load(char *name, u8 *address) {
	WORD read_size;
	FATFS ffs;
	FRESULT fres;

	fres = pf_mount(&ffs);
	if ( fres ) { return (fres<<16) | 1; }
	// fres = pf_open("u-boot.bin");
	fres = pf_open(name);
	if ( fres ) { return (fres<<16) | 2; }

	do {
		fres = pf_read(address,4096,&read_size);
		if ( fres ) { return (fres<<16) | 3; }
		address += read_size;
		offset += read_size;
		renderHexU32(45,29,(u32)offset);
	} while(read_size == 4096);
	return 0;
}

static void load_cart_id(void)
{
	u32 scratch;
	u32 id = 0;
	int i;

	for(i = GPIO_CART_CFG_HIGH; i >= GPIO_CART_CFG_LOW; i--)
		gpio_config_pin(GPIO_CART_CFG_PORT, i, GPIO_GPIOFN, 0, 0, 0);

	for(i = GPIO_CART_CFG_HIGH; i >= GPIO_CART_CFG_LOW; i--)
		id = (id<<1) + gpio_get_val(GPIO_CART_CFG_PORT, i);

	/* save into scratchpad register */
	scratch = gpio_get_scratchpad();
	scratch &= ~(BIT_MASK(GPIO_CART_CFG_HIGH-GPIO_CART_CFG_LOW+1) <<
			SCRATCH_CART_ID_POS);
	scratch |= (id<<SCRATCH_CART_ID_POS);
	gpio_set_scratchpad(scratch);
}
#else /* CPU_MP2530F */
#define load_board_id(...)
#define load_cart_id(...)
#endif

#define DET_MODE(value,bit) (value << ((bit)*2))

u8 do_menu(void)
{
	u8 selection = 0;
	u8 i;
	u8 pwrSwitchArmed = 0;

	u32 pwrDebounceCnt;
	u32 pwrState;
	u32 button;
	u32 mask_low;
	u32 mask_high;

	char *options[] = {
		"Boot from NAND normally",
		"Download via Xmodem @115200",
		"Load u-boot.bin from SD",
		"Load zImage from SD" };

	mask_low = ~(DET_MODE(3, BUTTON_UP_BIT) | DET_MODE(3, BUTTON_DN_BIT) | DET_MODE(3, BUTTON_A_BIT) | DET_MODE(3, BUTTON_B_BIT) | DET_MODE(3, BUTTON_LS_BIT));
	mask_high =  ~DET_MODE(3, BUTTON_PWR_BIT-16);

	// Make UP, DOWN, A, and B trigger on falling edge ( mode 2 )
	// Make powerand LS trigger on rising edge ( mode 3 )
	REG32(LF1000_GPIO_BASE+GPIOCDETMODE0) = (REG32(LF1000_GPIO_BASE+GPIOCDETMODE0) & mask_low) |
						DET_MODE(2, BUTTON_UP_BIT) | DET_MODE(2, BUTTON_DN_BIT) |
						DET_MODE(2, BUTTON_A_BIT) | DET_MODE(2, BUTTON_B_BIT) |
						DET_MODE(3, BUTTON_LS_BIT);
	// Power switch "bounces". We'll arm on rising edge, but debounce in handler
	REG32(LF1000_GPIO_BASE+GPIOCDETMODE1) = (REG32(LF1000_GPIO_BASE+GPIOCDETMODE1) & mask_high) |
						DET_MODE(3, BUTTON_PWR_BIT-16);
	
	// Write 1 to clear -- clear 'em all
	REG32(LF1000_GPIO_BASE+GPIOCDET) = REG32(LF1000_GPIO_BASE+GPIOCDET);

	while(1) {
		for ( i = 0; i < 4; i++ ) {
			fbsetInverse(0);
			renderString(2,6+i,(i == selection) ? "->" : "  ");
			fbsetInverse( i == selection );
			renderString(5,6+i,options[i]);
		}
		fbsetInverse(0);

		// now do nothing until a button is hit
		while ( (button = REG32(LF1000_GPIO_BASE+GPIOCDET)) == 0 );
		REG32(LF1000_GPIO_BASE+GPIOCDET) = button;

		if ( (button & BUTTON_UP_MSK) ) { selection = (selection-1)&0x3; }
		if ( (button & BUTTON_DN_MSK) ) { selection = (selection+1)&0x3; }
		if ( (button & BUTTON_A_MSK) || (button & BUTTON_B_MSK) ) return selection;
		if ( (button & BUTTON_PWR_MSK) ) {
			pwrDebounceCnt=0;
			pwrState = REG32(LF1000_GPIO_BASE+GPIOCPAD) & BUTTON_PWR_MSK;
			while ( pwrDebounceCnt++ < 0x20000 ) {
				// If we bounce, reset the counter
				if ( (REG32(LF1000_GPIO_BASE+GPIOCPAD) & BUTTON_PWR_MSK) != pwrState ) {
					pwrState = REG32(LF1000_GPIO_BASE+GPIOCPAD) & BUTTON_PWR_MSK;
					pwrDebounceCnt = 0;
				}
			}
			if ( (pwrState == 0) && pwrSwitchArmed ) die(); 	// trigger power down
			else if ( pwrState == BUTTON_PWR_MSK ) pwrSwitchArmed=1;// arm power down sequence
			// Clear any events that might be queued up.
			REG32(LF1000_GPIO_BASE+GPIOCDET) = REG32(LF1000_GPIO_BASE+GPIOCDET);
		}
	}
}

void guru_med(u32 v1, u32 v2)
{
	u32 i = 0;
	u8 rflip = 0x0;

        u32 *pwrmode = (u32 *)0xC000F07C;

	fb_showerror(v1, v2);

	while ( (REG32(LF1000_GPIO_BASE+GPIOCDET) & BUTTON_LS_MSK) == 0 ) {
		i++;
		if ( (i & 0x7FFFF) == 0 ) {
			mlc_set_palette_entry(0x3, rflip&0x1F, 0, 0);
			rflip = ~rflip;
		}
	}

        *pwrmode = 0x2000;
	// we should not live long beyond this point...
	while(1);
}

/*
 * main application
 */

/* Private values for rootfs flag */
#define RFS0 0
#define RFS1 1
#ifdef NFS_SUPPORT
#define NFS0 2
#define NFS1 3
#endif
int main(void)
{
	u32 rootfs;
	u8 *load_address;
	char *rfs_txt;
	u32 image = 0;
	struct jffs2_raw_inode *node, *mfg_node;
	char *cmdline = 0, *altcmdline = 0;
	u32 kernel_nand_addr = 0, alt_kernel_nand_addr = 0;
	int board_id;
	u32 ret = 0;
	u8 selection;
	u8 displayOn = 0;

#ifdef CPU_LF1000
	/* disable the USB controller */
	BIT_SET(REG16(LF1000_UDC_BASE+UDC_PCR), PCE);
#endif
	adc_init();
	board_id = load_board_id();
	display_backlight(board_id);
	clock_init();
	db_init();
#ifdef CONFIG_MACH_LF_LF1000
	/* now that backlight is on, see if we have enough battery to boot */
	if(gpio_get_val(LOW_BATT_PORT, LOW_BATT_PIN) == 0 && 
		ADC_TO_MV(adc_get_reading(LF1000_ADC_VBATSENSE)) < BOOT_MIN_MV){
		display_init();
		db_puts("PANIC: battery voltage too low!\n");
		guru_med(0xBA77DEAD,0x0BAD0BAD);
		// die();
	}
#endif /* CONFIG_MACH_LF_LF1000 */
#ifdef UBOOT_SUPPORT
	if(((REG32(LF1000_GPIO_BASE+GPIOCPAD) & BUTTON_MSK) == BUTTON_MSK)) {
		display_init();
		displayOn = 1;
		fbinit();
		fbclear();
	
		renderString(5,2,"OpenDidj lightning-boot " LB_VERSION "  /  " __DATE__ );
		renderString(5,4,"Select an option:");
		db_puts("OpenDidj lightning-boot " LB_VERSION "  /  " __DATE__ );
		db_puts("\n");

		make_crc_table();	

		timer_init();
		offset = 0;
//			tmr_poll_start(2000);
		db_puts("Switch to 115200 baud\n");

		/* set the baud rate */
		UART16(BRD) = 1; /* FIXME (for now "1"  sets 115200 baud , "11" sets 19200 baud) */
		UART16(UARTCLKGEN) = ((UARTDIV-1)<<UARTCLKDIV)|(UART_PLL<<UARTCLKSRCSEL);

		selection = do_menu();
		load_address = (u8 *)(UBOOT_ADDR);
		switch ( selection ) {
			case 0:
				goto normal_boot;
			case 1:
				xmodemInit(db_putchar,db_getc_async);
				ret = xmodemReceive(ubcopy);
				break;
			case 2:
				ret = sd_load("u-boot.bin",load_address);
				break;
			case 3:
				ret = sd_load("zImage",load_address); // try loading zImage at 3M
				break;
		}

		if ( ret != 0 ) guru_med(selection,ret);
		
		db_puts("boot jmp");
		/* jump to u-boot */
		((void (*)( int r0, int r1, int r2))load_address) 
			(0, MACH_TYPE_LF1000, 0);
		
		/* never get here! */
		guru_med(0x000000F0,0);
		// die();
	}
#endif /* UBOOT_SUPPORT */
normal_boot:
	/* Set up the kernel command line */

	/* read entire /flags partition */
	nand_read(fs_buffer, BOOT_FLAGS_ADDR, BOOT_FLAGS_SIZE);

	/* find rootfs file */
	node = jffs2_cat((char *)fs_buffer, BOOT_FLAGS_SIZE, "rootfs");
	rootfs = RFS0;
	if(node == 0) {
		db_puts("warning: failed to find rootfs flags!\n");
	}
	else {
		rfs_txt = (char*)node+sizeof(struct jffs2_raw_inode)-4;
		if(!strncmp(rfs_txt, "RFS1", 4)) {
			db_puts("booting RFS1\n");
			rootfs = RFS1;
		} 
#ifdef NFS_SUPPORT
		else if(!strncmp(rfs_txt, "NFS0", 4)) {
			db_puts("booting NFS0\n");
			rootfs = NFS0;
		} 
		else if(!strncmp(rfs_txt, "NFS1", 4)) {
			db_puts("booting NFS1\n");
			rootfs = NFS1;
		} 
#endif /* NFS_SUPPORT */
		else {
			db_puts("booting RFS0\n");
		}
	}

	/* Find the mfcart file */
	mfg_node = jffs2_cat((char *)fs_buffer, BOOT_FLAGS_SIZE, "mfcart");
	if(mfg_node != 0) {
		db_puts("Booting with mfg cartridge layout.\n");
	}

	/* construct the command line */
	if(mfg_node == 0) {
		if(rootfs == RFS0) {
			cmdline = CMDLINE_BASE CMDLINE_RFS0 CMDLINE_UBI;
			altcmdline = CMDLINE_BASE CMDLINE_RFS1 CMDLINE_UBI;
			kernel_nand_addr = BOOT0_ADDR;
			alt_kernel_nand_addr = BOOT1_ADDR;
			
		} 
		else if(rootfs == RFS1) {
			cmdline = CMDLINE_BASE CMDLINE_RFS1 CMDLINE_UBI;
			altcmdline = CMDLINE_BASE CMDLINE_RFS0 CMDLINE_UBI;
			kernel_nand_addr = BOOT1_ADDR;
			alt_kernel_nand_addr = BOOT0_ADDR;
		}
#ifdef NFS_SUPPORT
		else if(rootfs == NFS0) {
			cmdline = CMDLINE_BASE CMDLINE_NFS CMDLINE_UBI;
			altcmdline = CMDLINE_BASE CMDLINE_NFS CMDLINE_UBI;
			kernel_nand_addr = BOOT0_ADDR;
			alt_kernel_nand_addr = BOOT1_ADDR;
			
		} 
		else if(rootfs == NFS1) {
			cmdline = CMDLINE_BASE CMDLINE_NFS CMDLINE_UBI;
			altcmdline = CMDLINE_BASE CMDLINE_NFS CMDLINE_UBI;
			kernel_nand_addr = BOOT1_ADDR;
			alt_kernel_nand_addr = BOOT0_ADDR;
			
		} 
#endif /* NFS_SUPPORT */
	}
	
	if(tfs_load_summary(sum_buffer, kernel_nand_addr)) {
		db_puts("warning: booting alternative kernel!\n");
		if(tfs_load_summary(sum_buffer, alt_kernel_nand_addr)) {
			db_puts("PANIC: unable to load alt summary\n");
			guru_med(0xA0000000,1);
			//die();
		}
	}

	db_stopwatch_start("LOAD KERNEL");
	image = load_kernel(cmdline);
	db_stopwatch_stop();
	if(image == 0) {
		db_puts("Warning: booting alternative kernel!\n");
		if(tfs_load_summary(sum_buffer, alt_kernel_nand_addr) != 0) {
			guru_med(0xA0000000,2);
			//die();
		}
		image = load_kernel(altcmdline);
		if(image == 0) {
			db_puts("PANIC: nothing to boot\n");
			guru_med(0xA0000000,3);
			//die();
		}
	}

#ifdef DISPLAY_SUPPORT
	db_stopwatch_start("SPLASH");
	db_puts("Loading bootsplash\n");

	tfs_load_file("bootsplash.rgb", (u32 *)FRAME_BUFFER_ADDR);

	if ( !displayOn ) display_init();
	mlc_set_video_mode();

	//display_init();
	db_stopwatch_stop();
#endif

	load_cart_id();

	db_puts("Starting kernel...\n");
	cleanup_for_linux();
	/* jump to image (void, architecture ID, atags pointer) */
	((void(*)(int r0, int r1, unsigned int r2))image)
		(0, MACH_TYPE_LF1000, (unsigned int)params_buffer);

	/* never get here! */
	guru_med(0x000000F0,0);
	//die();
}
