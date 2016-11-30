/* Name: Erik Metzig
 *
 * csim.c - A cache simulator that can replay traces from Valgrind
 *     and output statistics such as number of hits, misses, and
 *     evictions.  The replacement policy is LRU.
 *
 * Implementation and assumptions:
 *  1. Each load/store can cause at most one cache miss. (I examined the trace,
 *  the largest request I saw was for 8 bytes).
 *  2. Instruction loads (I) are ignored, since we are interested in evaluating
 *  trans.c in terms of its data cache performance.
 *  3. data modify (M) is treated as a load followed by a store to the same
 *  address. Hence, an M operation can result in two cache hits, or a miss and a
 *  hit plus an possible eviction.
 *
 */
#include <getopt.h>
#include <stdlib.h>
#include <unistd.h>
#include <stdio.h>
#include <assert.h>
#include <math.h>
#include <limits.h>
#include <string.h>
#include <errno.h>
#include<stdbool.h>

#include "cachelab.h"

// #define DEBUG_ON 
#define ADDRESS_LENGTH 64

/****************************************************************************/

/* Globals set by command line args */
int verbosity = 0; /* print trace if set */
int s = 0; /* set index bits */
int b = 0; /* block offset bits */
int E = 0; /* associativity */
char* trace_file = NULL;

/* Derived from command line args */
int S; // number of sets S = 2^s
int B; // block size (bytes) B = 2^b

/* Counters used to record cache statistics */
int miss_count = 0;
int hit_count = 0;
int eviction_count = 0;
/*****************************************************************************/


/* Type: Memory address 
  */
typedef unsigned long long int mem_addr_t;

/* Type: Cache line
 * 
 * A structure for representing a line in a cache, contains a counter for 
 * tracking which line is the least recently used. 
 */
typedef struct cache_line {
   	 char valid;
   	 mem_addr_t tag;
	 int counter;
} cache_line_t;

typedef cache_line_t* cache_set_t;
typedef cache_set_t* cache_t;


/* The cache we are simulating */
cache_t cache;  

/*
 * Allocate data structures to hold info regrading the sets and cache lines
 * 
 * Initialize valid and tag field with 0s.
 *
 */
void initCache()
{
	//calculate S using the commandline arg
	S = pow(2, s);
	
	//allocate space for the number of sets
	cache = malloc(S * sizeof(cache_set_t));

	//iterate through sets, allocate space for lines
	for(int i = 0; i < S; i++) {

		cache[i] = malloc(E * sizeof(cache_line_t));
		
		//set the appropriate field values
		for(int j = 0; j < E; j++) {
		
			cache[i][j].valid = '0';
			cache[i][j].tag = 0;
			cache[i][j].counter = 0;
		}
	} 	
}


/*
 * freeCache - free each piece of memory  allocated using malloc 
 * inside initCache() function
 */
void freeCache()
{

	//recalculate in case initCache() not called
	S = pow(2, s);

	//iterate through the sets and free
	for(int i = 0; i < S; i++) {

		free(cache[i]);
	}
	
	//free the cache val itself
	free(cache);

}


/* 
 * accessData - Access data at memory address addr.
 *   If it is already in cache, increase hit_count
 *   If it is not in cache, bring it in cache, increase miss count.
 *   Increase eviction_count if a line is evicted.
 *   Manipulate data structures allocated in initCache() here
 */
void accessData(mem_addr_t addr)
{

	//mask address to isolate the set and tag
	mem_addr_t mask = pow(2, s + b);
	mask --;

	//set proper bits
	mask -= (pow(2, b) - 1);	
	
	//isolate set number
	mem_addr_t targSet = addr & mask;
	targSet = targSet >> b;
	
	//extract tag
	mem_addr_t targTag = addr >> (s + b);
	
	//int boolean variable if the cache will be a hit
	int found = 0;

	//values set to arbitrary numbers for finding desired lines
	int min = 5000;
	int max = 0;
	int minIndex = -1;
	
	//iterate  through all sets and find min and max counters
	for(int j = 0; j < E; j++) {

		//if it's the new min
		if(cache[targSet][j].counter < min) {

			min = cache[targSet][j].counter;
			minIndex = j;

		}

		//if it's the new max
		if(cache[targSet][j].counter > max) {

			max = cache[targSet][j].counter;
		}
	}

	//iterate through and find the line if possible
	for(int i = 0; i < E; i++) {

		//if it's valid and the correct tag
		if(cache[targSet][i].valid == '1' && cache[targSet][i].tag == targTag) {

			//it's found, increment
			found = 1;
			hit_count++;

			//set counter val
			cache[targSet][i].counter =  max + 1;
			break;
		}
	}
	

	//if no hits
	if(found == 0) {

		//then it's a miss
		miss_count++;

		//var for knowing if it's an eviction or not
		int foundEmpty = 0;

		//iterate through to find any that are empty
		for(int k = 0; k < E; k++) {

			//if an empty one is found
			if(cache[targSet][k].valid == '0') {

				//set that to the target
				cache[targSet][k].valid = '1';
				cache[targSet][k].tag = targTag;
				cache[targSet][k].counter = max + 1;
				
				//we know one is found
				foundEmpty = 1;
		
				break;
				
			}
		}

		//if no empty ones have been found
		if(foundEmpty == 0) {

			//we have to evict one
			eviction_count++;
		
			//evict the minimum counter value line
			cache[targSet][minIndex].tag = targTag;
			cache[targSet][minIndex].counter = max + 1;
		}		
	}	
}


/* 
 * replayTrace - replays the given trace file against the cache 
 * reads the input trace file line by line
 * extracts the type of each memory access : L/S/M
 * Translates one "L" as a load i.e. 1 memory access
 * Translates one "S" as a store i.e. 1 memory access
 * Translates one "M" as a load followed by a store i.e. 2 memory accesses 
 */
void replayTrace(char* trace_fn)
{

	//read trace file, make successive calls
    char buf[1000];
    mem_addr_t addr=0;
    unsigned int len=0;
    FILE* trace_fp = fopen(trace_fn, "r");

    if(!trace_fp){
        fprintf(stderr, "%s: %s\n", trace_fn, strerror(errno));
        exit(1);
    }

    while( fgets(buf, 1000, trace_fp) != NULL) {
        if(buf[1]=='S' || buf[1]=='L' || buf[1]=='M') {
            sscanf(buf+3, "%llx,%u", &addr, &len);
      
            if(verbosity)
                printf("%c %llx,%u ", buf[1], addr, len);

   

		//if it's a load, load
		if(buf[1] == 'L') {

			accessData(addr);
			
		}

		//if it's a store, store
		else if(buf[1] == 'S') {

			accessData(addr);
			
		}

		//otherwise, do data move and access
		else if(buf[1] == 'M') {

			accessData(addr);
			accessData(addr);

		}



            if (verbosity)
                printf("\n");
        }
    }

    fclose(trace_fp);
}

/*
 * printUsage - Print usage info
 */
void printUsage(char* argv[])
{
    printf("Usage: %s [-hv] -s <num> -E <num> -b <num> -t <file>\n", argv[0]);
    printf("Options:\n");
    printf("  -h         Print this help message.\n");
    printf("  -v         Optional verbose flag.\n");
    printf("  -s <num>   Number of set index bits.\n");
    printf("  -E <num>   Number of lines per set.\n");
    printf("  -b <num>   Number of block offset bits.\n");
    printf("  -t <file>  Trace file.\n");
    printf("\nExamples:\n");
    printf("  linux>  %s -s 4 -E 1 -b 4 -t traces/yi.trace\n", argv[0]);
    printf("  linux>  %s -v -s 8 -E 2 -b 4 -t traces/yi.trace\n", argv[0]);
    exit(0);
}

/*
 * main - Main routine 
 */
int main(int argc, char* argv[])
{
    char c;
    
    // Parse the command line arguments: -h, -v, -s, -E, -b, -t 
    while( (c=getopt(argc,argv,"s:E:b:t:vh")) != -1){
        switch(c){
        case 's':
            s = atoi(optarg);
            break;
        case 'E':
            E = atoi(optarg);
            break;
        case 'b':
            b = atoi(optarg);
            break;
        case 't':
            trace_file = optarg;
            break;
        case 'v':
            verbosity = 1;
            break;
        case 'h':
            printUsage(argv);
            exit(0);
        default:
            printUsage(argv);
            exit(1);
        }
    }

    /* Make sure that all required command line args were specified */
    if (s == 0 || E == 0 || b == 0 || trace_file == NULL) {
        printf("%s: Missing required command line argument\n", argv[0]);
        printUsage(argv);
        exit(1);
    }


    /* Initialize cache */
    initCache();

#ifdef DEBUG_ON
    printf("DEBUG: S:%u E:%u B:%u trace:%s\n", S, E, B, trace_file);
#endif
 
    replayTrace(trace_file);

    /* Free allocated memory */
    freeCache();

    /* Output the hit and miss statistics for the autograder */
    printSummary(hit_count, miss_count, eviction_count);
    return 0;
}
