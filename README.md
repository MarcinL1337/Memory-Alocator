# Memory-Alocator
Implementation of Memory Alocator
This implementation uses First-fit policy for finding new free block of memory, as well as segregated lists (segregated fits) for storing free blocks. Each free block consists of 4B footer, 4B header and payload all alligned to 16B which is the minimum size of a block. In both header and footer, information about size and flags are stored. Flags are stored at the 2 least significant bits and they consist of: a is_free flag (bit 0) and is_previous_free (bit 1). Each non-free block consists of 4B header with the same flags as free blocks and payload, all alligned to 16B. Non-free blocks don't use footers to decrease amount of internal fragmentation, as they're not necessary for an allocator to work properly.

This memory allocator is a university project for Operating Systems course. Main code is stored in file mm.c, the rest is a handout given by University.
