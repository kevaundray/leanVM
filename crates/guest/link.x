OUTPUT_ARCH(riscv)
ENTRY(_start)

/* No executable writes: code and constants have one RX PT_LOAD, all mutable
   storage has a disjoint RW PT_LOAD. Both use identity virtual/physical maps. */
PHDRS
{
    text PT_LOAD FLAGS(5);
    data PT_LOAD FLAGS(6);
}

SECTIONS
{
    . = 0x10000;
    .text : ALIGN(4)
    {
        KEEP(*(.text._start))
        *(.text .text.*)
    } :text
    .rodata : ALIGN(16)
    {
        *(.rodata .rodata.* .srodata .srodata.*)
        /* Keep high RAM addresses in near-code pointer slots: RV64 medany
           cannot form a PC-relative address more than 2 GiB from the code. */
        . = ALIGN(8);
        __heap_end_value = .;
        QUAD(__heap_end)
        __stack_top_value = .;
        QUAD(__stack_top)
    } :text

    . = ALIGN(0x1000);
    .data : ALIGN(16)
    {
        *(.data .data.*)
        __global_pointer$ = . + 0x800;
        *(.sdata .sdata.*)
        *(.got .got.*)
    } :data
    .bss (NOLOAD) : ALIGN(16)
    {
        __bss_start = .;
        *(.sbss .sbss.* .bss .bss.*)
        *(COMMON)
        . = ALIGN(16);
        __bss_end = .;
    } :data

    __stack_top = 0x100000000;
    __stack_bottom = __stack_top - 0x1000000;
    __heap_start = ALIGN(16);
    __heap_end = __stack_bottom;
    ASSERT(__heap_start <= __heap_end, "guest image overlaps reserved stack")
    .heap __heap_start (NOLOAD) :
    {
        . += __heap_end - __heap_start;
    } :data
    .stack __stack_bottom (NOLOAD) :
    {
        . += __stack_top - __stack_bottom;
    } :data

    /DISCARD/ :
    {
        *(.eh_frame .eh_frame_hdr .comment .note .note.*)
    }
}
