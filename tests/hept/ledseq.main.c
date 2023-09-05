#include <stdbool.h>
#include <stdio.h>
#include "ledseq.h"

static struct ledseq_task ledseqTaskMem;
static struct fun$step$ledseq_task ledseqTaskOut;

#define ANSI_COLOR_RED     "\x1b[31m"
#define ANSI_COLOR_GREEN   "\x1b[32m"
#define ANSI_COLOR_BLUE    "\x1b[34m"
#define ANSI_COLOR_RESET   "\x1b[0m"

int main() {
    fun$reset$ledseq_task(&ledseqTaskMem);

    while(true) {
        fun$step$ledseq_task(&ledseqTaskMem, &ledseqTaskOut, 0);
        if(ledseqTaskOut.led_state_led_green_l) {
            printf(ANSI_COLOR_GREEN "O" ANSI_COLOR_RESET);
        } else if(ledseqTaskOut.led_state_led_red_l) {
            printf(ANSI_COLOR_RED "O" ANSI_COLOR_RESET);
        } else {
            printf(".");
        }
        printf("     ");
        if(ledseqTaskOut.led_state_led_green_r) {
            printf(ANSI_COLOR_GREEN "O" ANSI_COLOR_RESET);
        } else if(ledseqTaskOut.led_state_led_red_r) {
            printf(ANSI_COLOR_RED "O" ANSI_COLOR_RESET);
        } else {
            printf(".");
        }
        printf("\n \\   /\n");
        printf("  \\ /\n");
        printf("   X\n");
        printf("  / \\\n");
        printf(" /   \\\n");
        fun$step$ledseq_task(&ledseqTaskMem, &ledseqTaskOut, 0);
        if(ledseqTaskOut.led_state_led_blue_l) {
            printf(ANSI_COLOR_BLUE "O" ANSI_COLOR_RESET);
        } else {
            printf(".");
        }
        printf("     ");
        if(ledseqTaskOut.led_state_led_blue_nrf) {
            printf(ANSI_COLOR_BLUE "O" ANSI_COLOR_RESET);
        } else {
            printf(".");
        }
        printf("\n");

        usleep(2000);
        printf("\e[1;1H\e[2J");
    }
    return 0;
}
