
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <inttypes.h>

#include "../../file_io.h"
#include "../../user_io.h"
#include "../../spi.h"
#include "../../hardware.h"
#include "../../menu.h"
#include "../../cheats.h"
#include "../../cfg.h"
#include "megacd.h"
#include "../physical_disc/physical_disc.h"

#define SAVE_IO_INDEX 5 // fake download to trigger save loading

#define MCD_GET_CMD        0
#define MCD_GET_SEND_DATA  1

// Spare CD_RESYNC words in the slot image hold the saved drive target and type.
#define MCD_SS_CTX_MAGIC 0x4D434454u
#define MCD_SS_CTX_WORD 558394u
#define MCD_M68K_W97_BYTE ((557314u + 97u) * 4u + 8u)
// Per slot: 1 after a save whose file is not written yet, 2 after a load echo.
static uint8_t mcd_ss_state[4] = {};
static uint32_t ss_watch_cnt[4] = {};
static uint8_t ss_watch_seen[4] = {};
static uint8_t last_req = 255;
static int mcd_ss_load_pending = 0;
static uint32_t mcd_ss_restore_ms = 0;
static uint64_t forced_status = 0;
static int forced_status_valid = 0;
static void mcd_restore_drive();

static void mcd_ss_sanitize(void* base)
{
	// wendReg with no pending bus cycle in SIDLE cannot complete after restore.
	uint32_t w;
	memcpy(&w, (uint8_t*)base + MCD_M68K_W97_BYTE, 4);
	if ((w & 0x1000) && !(w & 0x0100) && (w & 7) == 1) {
		w &= ~0x1000u;
		memcpy((uint8_t*)base + MCD_M68K_W97_BYTE, &w, 4);
	}
}

// Writes the drive context into a slot image right after the save, so a load that
// comes before the slot file is written still finds it.
static void mcd_ss_store_ctx(void* base)
{
	uint8_t* img = (uint8_t*)base;
	uint32_t magic = MCD_SS_CTX_MAGIC;
	uint32_t packed = (uint32_t)(cdd.status & 0xF) | (cdd.isData ? 0x10 : 0)
	                | ((uint32_t)(uint16_t)cdd.latency << 16);
	uint32_t lba = (uint32_t)cdd.lba;
	mcd_ss_sanitize(base);
	memcpy(img + 8 + (MCD_SS_CTX_WORD + 0) * 4, &magic, 4);
	memcpy(img + 8 + (MCD_SS_CTX_WORD + 1) * 4, &packed, 4);
	memcpy(img + 8 + (MCD_SS_CTX_WORD + 2) * 4, &lba, 4);
}

// The slot being loaded is the one whose counter changed since the last poll.
static void* mcd_ss_loaded_base()
{
	for (int i = 0; i < 4; i++) {
		uint32_t* b = (uint32_t*)process_ss_slot_ptr(i, MCD_SS_SIZE);
		if (b && ss_watch_seen[i] && b[0] != ss_watch_cnt[i]) return b;
	}
	return process_ss_last_changed_base(MCD_SS_SIZE);
}

static int mcd_ss_restore_guard()
{
	// Ignore the reset request sent by the restored core, but not an explicit mcd_reset().
	return mcd_ss_restore_ms && (GetTimer(0) - mcd_ss_restore_ms) < 2000;
}


static int need_reset=0;
static uint8_t has_command = 0;

void mcd_poll()
{
	static uint32_t poll_timer = 0;
	static uint8_t adj = 0;
	static uint32_t swap_close_at = 0;




	if (!poll_timer || CheckTimer(poll_timer))
	{
		// Restore the drive before the freeze check because the core waits for this handoff.
		int fpga_ready = mcd_can_send_data(1);
		int just_restored = 0;
		if (mcd_ss_load_pending) {
			mcd_restore_drive();
			mcd_ss_load_pending = 0;
			just_restored = 1;
		}

		// Capture the drive context before Update(), while the changed slot image is frozen.
		// A load echo already carries its context and must not be overwritten. A load of a
		// slot whose file is not written yet keeps it pending.
		for (int i = 0; i < 4; i++) {
			uint32_t* b = (uint32_t*)process_ss_slot_ptr(i, MCD_SS_SIZE);
			if (!b) { ss_watch_seen[i] = 0; continue; }
			if (!ss_watch_seen[i]) { ss_watch_seen[i] = 1; ss_watch_cnt[i] = b[0]; continue; }
			if (b[0] == ss_watch_cnt[i]) continue;
			// A load writes the counter just before it signals the load. Seen in between,
			// the change is left to the next poll, which restores the drive first.
			if (!just_restored) {
				mcd_can_send_data(1);
				if (mcd_ss_load_pending) break;
			}
			ss_watch_cnt[i] = b[0];
			if (just_restored) {
				if (mcd_ss_state[i] != 1) mcd_ss_state[i] = 2;
			} else {
				mcd_ss_state[i] = 1;
				if (b[1] == MCD_SS_WORDS) mcd_ss_store_ctx(b);
			}
		}

		if (!fpga_ready) {
			poll_timer = GetTimer(5);
			return;
		}
	}

	if (cdd.is_phys() && physical_disc_swap_consume() && cdd.SwapPhys())
	{
		cdd.isData = 1;
		cdd.status = CD_STAT_OPEN;      
		cdd.latency = 0;
		swap_close_at = GetTimer(PHYSICAL_DISC_SWAP_DWELL_MS);
	}
	if (cdd.is_phys() && swap_close_at && CheckTimer(swap_close_at))   
	{
		swap_close_at = 0;
		cdd.status = cdd.loaded ? CD_STAT_STOP : CD_STAT_NO_DISC;   
		cdd.latency = 10;
	}

	int paced = !cdd.isData && cdd.status == CD_STAT_PLAY && cdd.latency == 0 && cfg.megacd_cdda_paced;
	if (paced && poll_timer && CheckTimer(poll_timer) && !mcd_can_send_data(0))   // 0: audio track (isData is 0)
	{
		// MEGACD_CDDA_PACED=1: the audio buffer is full. Hold back the status too, and try again in 1 ms,
		// so that every status (CDD interrupt) comes with exactly one sector of subcode, as on a real drive.
		poll_timer = GetTimer(1);
	}
	else if (!poll_timer || CheckTimer(poll_timer))
	{
		if (paced) {
			// MEGACD_CDDA_PACED=1: one audio sector (and its subcode) with each status, every 13.25 ms
			// (13,13,13,14), close to the 75 sectors per second of a real drive, so the subcode reaches the
			// BIOS at a steady rate (CD+G). The next poll is set from the previous one, so a late poll is
			// caught up; slightly faster than 75 Hz so the audio buffer stays filled.
			static uint8_t paced_adj = 0;
			uint32_t next = poll_timer + 13 + (paced_adj == 3 ? 1 : 0);
			if (++paced_adj >= 4) paced_adj = 0;
			if (CheckTimer(next + 50)) next = GetTimer(13);
			poll_timer = next;
			adj = 0;
		} else if (!cdd.isData && cdd.status == CD_STAT_PLAY && cdd.latency == 0) {
			// Send audio sectors faster so buffer stays filled
			poll_timer = GetTimer(10);
			adj = 0;
		} else {
			poll_timer = GetTimer(13 + (!adj ? 1 : 0));
			if (++adj >= 3) adj = 0;
		}

		if (has_command) {
			spi_uio_cmd_cont(UIO_CD_SET);
			uint64_t s = forced_status_valid ? forced_status : cdd.GetStatus(0);
			forced_status_valid = 0;
			spi_w((s >> 0) & 0xFFFF);
			spi_w((s >> 16) & 0xFFFF);
			spi_w(((s >> 32) & 0x00FF) | (cdd.isData ? 0x01 << 8 : 0x00 << 8));
			DisableIO();

			has_command = 0;

			//printf("\x1b[32mMCD: Send status, status = %04X%04X%04X, frame = %u\n\x1b[0m", (uint16_t)((s >> 32) & 0x00FF), (uint16_t)((s >> 16) & 0xFFFF), (uint16_t)((s >> 0) & 0xFFFF), frame);
		}

		cdd.Update();
	}


	uint8_t req = spi_uio_cmd_cont(UIO_CD_GET);
	if (req != last_req)
	{
		last_req = req;

		spi_w(MCD_GET_CMD);

		uint16_t data_in[4];
		data_in[0] = spi_w(0);
		data_in[1] = spi_w(0);
		data_in[2] = spi_w(0);
		DisableIO();

		if (need_reset || (data_in[0] == 0xFF && !mcd_ss_restore_guard())) {
			printf("MCD: request to reset\n");
			need_reset = 0;
			cdd.Reset();
		}

		uint64_t c = *((uint64_t*)(data_in));
		cdd.SetCommand(c, 0);
		cdd.CommandExec();
		has_command = 1;


		//printf("\x1b[32mMCD: Get command, command = %04X%04X%04X, has_command = %u\n\x1b[0m", data_in[2], data_in[1], data_in[0], has_command);
	}
	else
		DisableIO();
}

static char buf[1024];
static void mcd_mount_save(const char *filename)
{
	user_io_set_index(SAVE_IO_INDEX);
	user_io_set_download(1);
	if (strlen(filename))
	{
		FileGenerateSavePath(filename, buf);
		user_io_file_mount(buf, 0, 1);
	}
	else
	{
		user_io_file_mount("");
	}
	user_io_set_download(0);
}

static int mcd_load_rom(const char *basename, const char *name, int sub_index)
{
	strcpy(buf, basename);
	char *p = strrchr(buf, '/');
	if (p)
	{
		p++;
		strcpy(p, name);
		if (user_io_file_tx(buf, sub_index << 6)) return 1;
	}

	return 0;
}

int mcd_set_image(int num, const char *filename)
{
	static char last_dir[1024] = {};

	(void)num;

	cdd.Unload();
	physical_disc_swap_enable(0);              
	cdd.status = CD_STAT_OPEN;

	int phys = !strcmp(filename, PHYSICAL_DISC_SENTINEL);
	int audio_only = 0;
	physical_disc_region_t disc_region = PHYSICAL_DISC_REGION_UNKNOWN;





	if (phys && !physical_disc_open(NULL))
	{
		toc_t disc_toc = {};
		if (!physical_disc_load_toc(&disc_toc)) audio_only = physical_disc_toc_audio_only(&disc_toc);
		if (!audio_only) disc_region = physical_disc_region();



		if (!physical_disc_disc_present()) physical_disc_close();
	}

	int same_game = *filename && *last_dir && !strncmp(last_dir, filename, strlen(last_dir));





	if (phys) same_game = 0;
	// Reset the savestate session state on a game change. Main stays running across mounts.
	if (!same_game)
	{
		memset(mcd_ss_state, 0, sizeof(mcd_ss_state));
		memset(ss_watch_cnt, 0, sizeof(ss_watch_cnt));
		memset(ss_watch_seen, 0, sizeof(ss_watch_seen));
		has_command = 0;
		forced_status_valid = 0;
		last_req = 255;
		mcd_ss_load_pending = 0;
		mcd_ss_restore_ms = 0;
	}

	strcpy(last_dir, filename);
	char *p = strrchr(last_dir, '/');
	if (p) *p = 0;

	int loaded = 1;
	if (!same_game)
	{
		mcd_mount_save("");

		user_io_status_set("[0]", 1);
		user_io_status_set("[0]", 0);
		mcd_reset();

		loaded = 0;
		if (phys)
		{




			const char *rn = physical_disc_region_name(disc_region);
			if (*rn)
			{
				sprintf(buf, "%s/boot_%s.rom", HomeDir(), rn);
				loaded = user_io_file_tx(buf);
				if (!loaded)
				{
					sprintf(buf, "%s/bios_%s.rom", HomeDir(), rn);
					loaded = user_io_file_tx(buf);
				}
			}
			printf("\x1b[32mMCD: physical disc region %s%s\n\x1b[0m",
				*rn ? rn : "unknown",
				loaded ? ", loaded matching BIOS" : ", falling back to boot.rom");
		}
		else
		{
			strcpy(buf, last_dir);
			char *bp = strrchr(buf, '/');
			if (bp)
			{
				strcpy(bp + 1, "cd_bios.rom");
				loaded = user_io_file_tx(buf);
			}
		}

		if (!loaded)
		{
			sprintf(buf, "%s/boot.rom", HomeDir());
			loaded = user_io_file_tx(buf);




			if (loaded && phys && !audio_only && disc_region != PHYSICAL_DISC_REGION_UNKNOWN)
			{
				static uint8_t hdr[0x200];
				physical_disc_region_t bios_region = PHYSICAL_DISC_REGION_UNKNOWN;

				if (FileLoad(buf, hdr, sizeof(hdr)) >= 0x1F3)
					bios_region = physical_disc_region_from_md_header(hdr, sizeof(hdr));

				if (bios_region != PHYSICAL_DISC_REGION_UNKNOWN && bios_region != disc_region)
				{
					static char msg[128];
					sprintf(msg, "%s disc on %s BIOS - add boot_%s.rom",
						physical_disc_region_name(disc_region),
						physical_disc_region_name(bios_region),
						physical_disc_region_name(disc_region));
					printf("\x1b[32mMCD: WARNING: %s\n\x1b[0m", msg);
					Info(msg, 6000);
				}
			}
		}

		if (!loaded) Info("CD BIOS not found!", 4000);
	}

	int mounted = 0;
	if (loaded && *filename)
	{
		if (cdd.Load(filename) > 0)
		{
			mounted = 1;
			cdd.isData = audio_only ? 0 : 1;
			cdd.status = cdd.loaded ? CD_STAT_STOP : CD_STAT_NO_DISC;
			cdd.latency = 10;
			cdd.SendData = mcd_send_data;
			cdd.CanSendData = mcd_can_send_data;
			if (phys) physical_disc_swap_enable(1);   

			if (!audio_only && !same_game)
			{
				if (phys)
				{


					char save_name[64] = "physical_disc";
					physical_disc_save_name(PHYSICAL_DISC_DISC_MEGACD, save_name, sizeof(save_name));
					mcd_mount_save(save_name);
				}
				else
				{
					mcd_load_rom(filename, "cd_bios.rom", 0);
					mcd_load_rom(filename, "cart.rom", 1);
					mcd_mount_save(filename);
					cheats_init(filename, 0);
				}
			}
			char state_name[64] = "physical_disc";
			if (phys) physical_disc_save_name(PHYSICAL_DISC_DISC_MEGACD, state_name, sizeof(state_name));
			process_ss(phys ? state_name : filename);
			for (int i = 0; i < 4; i++) {
				void* b = process_ss_slot_ptr(i, MCD_SS_SIZE);
				if (b) mcd_ss_sanitize(b);
			}
		}
		else
		{
			cdd.status = CD_STAT_NO_DISC;
		}
	}



	return mounted;
}

void mcd_reset() {
	need_reset = 1;
}

int mcd_send_data(uint8_t* buf, int len, uint8_t index) {
	// set index byte
	user_io_set_index(index);

	user_io_set_download(1);
	user_io_file_tx_data(buf, len);
	user_io_set_download(0);
	return 1;
}

static char int_blank[] = {
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x5F, 0x5F, 0x5F, 0x5F, 0x5F, 0x5F, 0x5F, 0x5F, 0x5F, 0x5F, 0x5F, 0x00, 0x00, 0x00, 0x00, 0x40,
	0x00, 0x7D, 0x00, 0x7D, 0x00, 0x7D, 0x00, 0x7D, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x53, 0x45, 0x47, 0x41, 0x5F, 0x43, 0x44, 0x5F, 0x52, 0x4F, 0x4D, 0x00, 0x01, 0x00, 0x00, 0x00,
	0x52, 0x41, 0x4D, 0x5F, 0x43, 0x41, 0x52, 0x54, 0x52, 0x49, 0x44, 0x47, 0x45, 0x5F, 0x5F, 0x5F,
};

static char ext_blank[] = {
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x5F, 0x5F, 0x5F, 0x5F, 0x5F, 0x5F, 0x5F, 0x5F, 0x5F, 0x5F, 0x5F, 0x00, 0x00, 0x00, 0x00, 0x40,
	0x1F, 0xFD, 0x1F, 0xFD, 0x1F, 0xFD, 0x1F, 0xFD, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x53, 0x45, 0x47, 0x41, 0x5F, 0x43, 0x44, 0x5F, 0x52, 0x4F, 0x4D, 0x00, 0x01, 0x00, 0x00, 0x00,
	0x52, 0x41, 0x4D, 0x5F, 0x43, 0x41, 0x52, 0x54, 0x52, 0x49, 0x44, 0x47, 0x45, 0x5F, 0x5F, 0x5F,
};

void mcd_fill_blanksave(uint8_t *buffer, uint32_t lba)
{
	if (lba == 0xF)
	{
		memcpy(buffer, int_blank, 512);
	}
	else if (lba == 0x40F)
	{
		memcpy(buffer, ext_blank, 512);
	}
	else
	{
		memset(buffer, 0, 512);
	}
}

int mcd_can_send_data(uint8_t type) {
	// Data and audio delivery both stop while the core is frozen.

	// Ask the FPGA if it is ready to receive a sector
	spi_uio_cmd_cont(UIO_CD_GET);
	spi_w(MCD_GET_SEND_DATA | (type << 2));

	uint16_t data = spi_w(0);
	DisableIO();

	mcd_ss_load_pending = (data >> 1) & 1;
	return data & 1;
}

// Returns 0 when the counter change is the core's echo of a load: the slot image is
// then what was read from the file, and writing it back would only rewrite the file.
int mcd_ss_presave(void* base, int slot)
{
	if (!base || slot < 0 || slot > 3) return 1;
	if (mcd_ss_state[slot] == 2) {
		mcd_ss_state[slot] = 0;
		return 0;
	}
	// mcd_poll() has written the drive context of a new save into the image already.
	mcd_ss_sanitize(base);
	mcd_ss_state[slot] = 0;
	return 1;
}

static void mcd_restore_drive()
{
	mcd_ss_restore_ms = GetTimer(0);
	spi_uio_cmd_cont(UIO_CD_GET);
	spi_w(2); // Saved CDD status. Reading the third word acknowledges FW_HOLD.
	uint16_t w0 = spi_w(0);
	uint16_t w1 = spi_w(0);
	uint16_t w2 = spi_w(0);
	DisableIO();

	uint64_t s = ((uint64_t)(w2 & 0xFF) << 32) | ((uint32_t)w1 << 16) | w0;
	uint8_t status = s & 0xF;
	uint8_t s1 = (s >> 4) & 0xF;

	uint8_t* img = (uint8_t*)mcd_ss_loaded_base();
	uint32_t rw2 = 0;
	if (img) memcpy(&rw2, img + 8 + 558392u * 4, 4);
	// Last non-IDLE command handed to the drive before the save, 0 if the core does not save it.
	uint8_t lastcmd = (rw2 >> 24) & 0xF;

	// A seek packet holds the old position and other reports can carry a stale
	// type nibble. A packet that does not match the last play or seek command
	// answers an earlier command. In these cases use the drive context saved in the slot.
	if (img) {
		uint32_t magic, packed, ulba;
		memcpy(&magic, img + 8 + (MCD_SS_CTX_WORD + 0) * 4, 4);
		memcpy(&packed, img + 8 + (MCD_SS_CTX_WORD + 1) * 4, 4);
		memcpy(&ulba, img + 8 + (MCD_SS_CTX_WORD + 2) * 4, 4);
		int lba = (int)ulba;
		uint8_t cstat = packed & 0xF;
		int ctx_is_data = (packed >> 4) & 1;
		int packet_is_data = (((s >> 32) & 0xF) == 0x4);
		int stat_ok = (cstat == CD_STAT_PLAY || cstat == CD_STAT_SEEK ||
		               cstat == CD_STAT_PAUSE);
		// Plays usually start in the pregap before the target, at a negative LBA.
		int ctx_ok = (magic == MCD_SS_CTX_MAGIC && stat_ok &&
		              lba >= -150 && lba + 150 < 80 * 60 * 75);
		int stale = ((lastcmd == CD_COMM_PLAY || lastcmd == CD_COMM_TRACK_PLAY) && status != CD_STAT_PLAY) ||
		            (lastcmd == CD_COMM_SEEK && status != CD_STAT_PAUSE);
		if (ctx_ok && (status == CD_STAT_SEEK || stale || ctx_is_data != packet_is_data)) {
			int lba150 = lba + 150;
			int m = (lba150 / 75) / 60, sec = (lba150 / 75) % 60, f = lba150 % 75;
			uint8_t d2 = m / 10, d3 = m % 10, d4 = sec / 10, d5 = sec % 10,
			        d6 = f / 10, d7 = f % 10;
			uint64_t c = (uint64_t)CD_COMM_PLAY
			           | ((uint64_t)d2 << 8) | ((uint64_t)d3 << 12)
			           | ((uint64_t)d4 << 16) | ((uint64_t)d5 << 20)
			           | ((uint64_t)d6 << 24) | ((uint64_t)d7 << 28);
			c |= (uint64_t)((~(CD_COMM_PLAY + d2 + d3 + d4 + d5 + d6 + d7)) & 0xF) << 36;
			cdd.SetCommand(c, 0);
			cdd.CommandExec();
			if (cstat != CD_STAT_PLAY) {
				cdd.SetCommand(CD_COMM_PAUSE | ((uint64_t)((~CD_COMM_PAUSE) & 0xF) << 36), 0);
				cdd.CommandExec();
			}
			cdd.latency = 0;
			goto proactive;
		}
	}

	if (s1 != 0) return; // No absolute MSF in the packet.

	// CDC data headers use byte-order BCD. Audio status uses stat[] nibble order.
	// Declared without initializers so the goto above does not cross them.
	int is_data, m, sec, f;
	is_data = (((s >> 32) & 0xF) == 0x4);
	if (is_data) {
		m   = (int)((s >> 28) & 0xF) * 10 + (int)((s >> 24) & 0xF);
		sec = (int)((s >> 20) & 0xF) * 10 + (int)((s >> 16) & 0xF);
		f   = (int)((s >> 12) & 0xF) * 10 + (int)((s >>  8) & 0xF);
	} else {
		m   = (int)((s >>  8) & 0xF) * 10 + (int)((s >> 12) & 0xF);
		sec = (int)((s >> 16) & 0xF) * 10 + (int)((s >> 20) & 0xF);
		f   = (int)((s >> 24) & 0xF) * 10 + (int)((s >> 28) & 0xF);
	}

	// If the CDC header is torn, use the last absolute position saved with the status.
	{
		int msf_ok = 1;
		for (int i = 2; i <= 7; i++)
			if (((s >> (i * 4)) & 0xF) > 9) msf_ok = 0;
		if (msf_ok && (m > 79 || sec >= 60 || f >= 75)) msf_ok = 0;
		if (!msf_ok) {
			// Bits 27:24 hold the last command, so check only the MSF bits.
			uint64_t alt = ((uint64_t)(rw2 & 0xFFFFFF)) << 8;
			int am = (int)((alt >> 8) & 0xF) * 10 + (int)((alt >> 12) & 0xF);
			int as = (int)((alt >> 16) & 0xF) * 10 + (int)((alt >> 20) & 0xF);
			int af = (int)((alt >> 24) & 0xF) * 10 + (int)((alt >> 28) & 0xF);
			int alt_ok = ((rw2 & 0xFFFFFF) != 0);
			for (int i = 2; i <= 7; i++)
				if (((alt >> (i * 4)) & 0xF) > 9) alt_ok = 0;
			if (alt_ok && (am > 79 || as >= 60 || af >= 75)) alt_ok = 0;
			if (alt_ok) {
				m = am; sec = as; f = af;
			} else {
				printf("MCD: savestate load - no valid MSF, drive left as-is\n");
				goto proactive;
			}
		}
	}

	{
		// The decoded data sector was already consumed, so resume at the next one.
		if (is_data) {
			if (++f >= 75) { f = 0; if (++sec >= 60) { sec = 0; m++; } }
		}
		uint8_t d2 = m / 10, d3 = m % 10, d4 = sec / 10, d5 = sec % 10,
		        d6 = f / 10, d7 = f % 10;
		uint64_t c = (uint64_t)CD_COMM_PLAY
		           | ((uint64_t)d2 << 8) | ((uint64_t)d3 << 12)
		           | ((uint64_t)d4 << 16) | ((uint64_t)d5 << 20)
		           | ((uint64_t)d6 << 24) | ((uint64_t)d7 << 28);
		c |= (uint64_t)((~(CD_COMM_PLAY + d2 + d3 + d4 + d5 + d6 + d7)) & 0xF) << 36;
		cdd.SetCommand(c, 0);
		cdd.CommandExec();
		if (status != CD_STAT_PLAY) {
			cdd.SetCommand(CD_COMM_PAUSE | ((uint64_t)((~CD_COMM_PAUSE) & 0xF) << 36), 0);
			cdd.CommandExec();
		}
		// The restored game driver must not see an extra seek delay.
		cdd.latency = 0;
	}

proactive:
	// Answer a pending CDD request with the saved status report as is.
	if (img) {
		uint32_t rw0, rw1;
		memcpy(&rw0, img + 8 + 558390u * 4, 4);
		memcpy(&rw1, img + 8 + 558391u * 4, 4);
		forced_status = ((uint64_t)(rw1 & 0xFF) << 32) | rw0;
		forced_status_valid = 1;
	}
	has_command = 1;
}
