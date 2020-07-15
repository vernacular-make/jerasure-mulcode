/* *
 * Copyright (c) 2014, James S. Plank and Kevin Greenan
 * All rights reserved.
 *
 * Jerasure - A C/C++ Library for a Variety of Reed-Solomon and RAID-6 Erasure
 * Coding Techniques
 *
 * Revision 2.0: Galois Field backend now links to GF-Complete
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 *  - Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 *  - Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in
 *    the documentation and/or other materials provided with the
 *    distribution.
 *
 *  - Neither the name of the University of Tennessee nor the names of its
 *    contributors may be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
 * BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS
 * OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED
 * AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY
 * WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 */

/* Jerasure's authors:

   Revision 2.x - 2014: James S. Plank and Kevin M. Greenan.
   Revision 1.2 - 2008: James S. Plank, Scott Simmerman and Catherine D. Schuman.
   Revision 1.0 - 2007: James S. Plank.
 */

/* 

This program takes as input an inputfile, k, m, a coding 
technique, w, and packetsize.  It creates k+m files from 
the original file so that k of these files are parts of 
the original file and m of the files are encoded based on 
the given coding technique. The format of the created files 
is the file name with "_k#" or "_m#" and then the extension.  
(For example, inputfile test.txt would yield file "test_k1.txt".)
*/

#include <assert.h>
#include <time.h>
#include <sys/time.h>
#include <sys/stat.h>
#include <unistd.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <errno.h>
#include <signal.h>
#include <gf_rand.h>
#include <unistd.h>
#include "jerasure.h"
#include "reed_sol.h"
#include "cauchy.h"
#include "liberation.h"
#include "timing.h"

#define N 10
#define M 8
#define r 2
enum Coding_Technique {Reed_Sol_Van, Reed_Sol_R6_Op, Cauchy_Orig, Cauchy_Good, Liberation, Blaum_Roth, Liber8tion, RDP, EVENODD, No_Coding};

char *Methods[N] = {"reed_sol_van", "reed_sol_r6_op", "cauchy_orig", "cauchy_good", "liberation", "blaum_roth", "liber8tion", "no_coding"};

/* Global variables for signal handler */
int readins, n;
enum Coding_Technique method;

/* Function prototypes */
int is_prime(int w);
void ctrl_bs_handler(int dummy);

int jfread(void *ptr, int size, int nmembers, FILE *stream)
{
  if (stream != NULL) return fread(ptr, size, nmembers, stream);

  MOA_Fill_Random_Region(ptr, size);
  return size;
}

static void print_data_and_coding(int k, int m, int w, int size,
	char **data, char **coding)
{
	int i, j, x;
	int n, sp;
	long l;

	if (k > m) n = k;
	else n = m;
	sp = size * 2 + size / (w / 8) + 8;

	printf("%-*sCoding\n", sp, "Data");
	for (i = 0; i < n; i++) {
		if (i < k) {
			printf("D%-2d:", i);
			for (j = 0; j < size; j += (w / 8)) {
				printf(" ");
				for (x = 0; x < w / 8; x++) {
					printf("%02x", (unsigned char)data[i][j + x]);
				}
			}
			printf("    ");
		}
		else printf("%*s", sp, "");
		if (i < m) {
			printf("C%-2d:", i);
			for (j = 0; j < size; j += (w / 8)) {
				printf(" ");
				for (x = 0; x < w / 8; x++) {
					printf("%02x", (unsigned char)coding[i][j + x]);
				}
			}
		}
		printf("\n");
	}
	printf("\n");
}

int main (int argc, char **argv) {
	FILE *fp, *fp2;				// file pointers
	char *block;				// padding file
	int size, newsize;			// size of file and temp size 
	struct stat status;			// finding file size

	
	enum Coding_Technique tech;		// coding technique (parameter)
	int k, m, w, packetsize;		// parameters
	int buffersize;					// paramter
	int i,j,i1,j1;						// loop control variables
	int blocksize;					// size of k+m files
	int total;
	int extra; 
	int stripe_size;
	
	/* Jerasure Arguments */
	char **data;				
	char **coding;
        char **fdata;
        char **fcoding;
        char **ffdata;
        char **ccoding;
        char *e;
        
        char *extra1;
        char *extra2;
        char *extra3;
	int *matrix;
	int *bitmatrix;
	int **schedule;
	
	/* Creation of file name variables */
	char temp[5];
	char *s1, *s2, *extension;
	char *fname;
	int md;
	char *curdir;
	
	/* Timing variables */
	struct timing t1, t2, t3, t4;
	double tsec;
	double totalsec;
	struct timing start;

	/* Find buffersize */
	int up, down;


	signal(SIGQUIT, ctrl_bs_handler);

	/* Start timing */
	timing_set(&t1);
	totalsec = 0.0;
	matrix = NULL;
	bitmatrix = NULL;
	schedule = NULL;
	
	/* Error check Arguments*/
	if (argc != 8) {
		fprintf(stderr,  "usage: inputfile k m coding_technique w packetsize buffersize\n");
		fprintf(stderr,  "\nChoose one of the following coding techniques: \nreed_sol_van, \nreed_sol_r6_op, \ncauchy_orig, \ncauchy_good, \nliberation, \nblaum_roth, \nliber8tion");
		fprintf(stderr,  "\n\nPacketsize is ignored for the reed_sol's");
		fprintf(stderr,  "\nBuffersize of 0 means the buffersize is chosen automatically.\n");
		fprintf(stderr,  "\nIf you just want to test speed, use an inputfile of \"-number\" where number is the size of the fake file you want to test.\n\n");
		exit(0);
	}
	/* Conversion of parameters and error checking */	
	if (sscanf(argv[2], "%d", &k) == 0 || k <= 0) {
		fprintf(stderr,  "Invalid value for k\n");
		exit(0);
	}
	if (sscanf(argv[3], "%d", &m) == 0 || m < 0) {
		fprintf(stderr,  "Invalid value for m\n");
		exit(0);
	}
	if (sscanf(argv[5],"%d", &w) == 0 || w <= 0) {
		fprintf(stderr,  "Invalid value for w.\n");
		exit(0);
	}
	if (argc == 6) {
		packetsize = 0;
	}
	else {
		if (sscanf(argv[6], "%d", &packetsize) == 0 || packetsize < 0) {
			fprintf(stderr,  "Invalid value for packetsize.\n");
			exit(0);
		}
	}
	if (argc != 8) {
		buffersize = 0;
	}
	else {
		if (sscanf(argv[7], "%d", &buffersize) == 0 || buffersize < 0) {
			fprintf(stderr, "Invalid value for buffersize\n");
			exit(0);
		}
		
	}

	/* Determine proper buffersize by finding the closest valid buffersize to the input value  */
	if (buffersize != 0) {
		if (packetsize != 0 && buffersize%(sizeof(long)*w*k*packetsize) != 0) { 
			up = buffersize;
			down = buffersize;
			while (up%(sizeof(long)*w*k*packetsize) != 0 && (down%(sizeof(long)*w*k*packetsize) != 0)) {
				up++;
				if (down == 0) {
					down--;
				}
			}
			if (up%(sizeof(long)*w*k*packetsize) == 0) {
				buffersize = up;
			}
			else {
				if (down != 0) {
					buffersize = down;
				}
			}
		}
		else if (packetsize == 0 && buffersize%(sizeof(long)*w*k) != 0) {
			up = buffersize;
			down = buffersize;
			while (up%(sizeof(long)*w*k) != 0 && down%(sizeof(long)*w*k) != 0) {
				up++;
				down--;
			}
			if (up%(sizeof(long)*w*k) == 0) {
				buffersize = up;
			}
			else {
				buffersize = down;
			}
		}
	}

	/* Setting of coding technique and error checking */
	
	if (strcmp(argv[4], "no_coding") == 0) {
		tech = No_Coding;
	}
	else if (strcmp(argv[4], "reed_sol_van") == 0) {
		tech = Reed_Sol_Van;
		if (w != 8 && w != 16 && w != 32) {
			fprintf(stderr,  "w must be one of {8, 16, 32}\n");
			exit(0);
		}
	}
	else if (strcmp(argv[4], "reed_sol_r6_op") == 0) {
		if (m != 2) {
			fprintf(stderr,  "m must be equal to 2\n");
			exit(0);
		}
		if (w != 8 && w != 16 && w != 32) {
			fprintf(stderr,  "w must be one of {8, 16, 32}\n");
			exit(0);
		}
		tech = Reed_Sol_R6_Op;
	}
	else if (strcmp(argv[4], "cauchy_orig") == 0) {
		tech = Cauchy_Orig;
		if (packetsize == 0) {
			fprintf(stderr, "Must include packetsize.\n");
			exit(0);
		}
	}
	else if (strcmp(argv[4], "cauchy_good") == 0) {
		tech = Cauchy_Good;
		if (packetsize == 0) {
			fprintf(stderr, "Must include packetsize.\n");
			exit(0);
		}
	}
	else if (strcmp(argv[4], "liberation") == 0) {
		if (k > w) {
			fprintf(stderr,  "k must be less than or equal to w\n");
			exit(0);
		}
		if (w <= 2 || !(w%2) || !is_prime(w)) {
			fprintf(stderr,  "w must be greater than two and w must be prime\n");
			exit(0);
		}
		if (packetsize == 0) {
			fprintf(stderr, "Must include packetsize.\n");
			exit(0);
		}
		if ((packetsize%(sizeof(long))) != 0) {
			fprintf(stderr,  "packetsize must be a multiple of sizeof(long)\n");
			exit(0);
		}
		tech = Liberation;
	}
	else if (strcmp(argv[4], "blaum_roth") == 0) {
		if (k > w) {
			fprintf(stderr,  "k must be less than or equal to w\n");
			exit(0);
		}
		if (w <= 2 || !((w+1)%2) || !is_prime(w+1)) {
			fprintf(stderr,  "w must be greater than two and w+1 must be prime\n");
			exit(0);
		}
		if (packetsize == 0) {
			fprintf(stderr, "Must include packetsize.\n");
			exit(0);
		}
		if ((packetsize%(sizeof(long))) != 0) {
			fprintf(stderr,  "packetsize must be a multiple of sizeof(long)\n");
			exit(0);
		}
		tech = Blaum_Roth;
	}
	else if (strcmp(argv[4], "liber8tion") == 0) {
		if (packetsize == 0) {
			fprintf(stderr, "Must include packetsize\n");
			exit(0);
		}
		if (w != 8) {
			fprintf(stderr, "w must equal 8\n");
			exit(0);
		}
		if (m != 2) {
			fprintf(stderr, "m must equal 2\n");
			exit(0);
		}
		if (k > w) {
			fprintf(stderr, "k must be less than or equal to w\n");
			exit(0);
		}
		tech = Liber8tion;
	}
	else {
		fprintf(stderr,  "Not a valid coding technique. Choose one of the following: reed_sol_van, reed_sol_r6_op, cauchy_orig, cauchy_good, liberation, blaum_roth, liber8tion, no_coding\n");
		exit(0);
	}

	/* Set global variable method for signal handler */
	method = tech;

	/* Get current working directory for construction of file names */
	curdir = (char*)malloc(sizeof(char)*1000);	
	assert(curdir == getcwd(curdir, 1000));

        if (argv[1][0] != '-') {

		/* Open file and error check */
		fp = fopen(argv[1], "rb");
		if (fp == NULL) {
			fprintf(stderr,  "Unable to open file.\n");
			exit(0);
		}
	
		/* Create Coding directory */
		i = mkdir("Coding", S_IRWXU);
		if (i == -1 && errno != EEXIST) {
			fprintf(stderr, "Unable to create Coding directory.\n");
			exit(0);
		}
	
		/* Determine original size of file */
		stat(argv[1], &status);	
		size = status.st_size;
        } else {
        	if (sscanf(argv[1]+1, "%d", &size) != 1 || size <= 0) {
                	fprintf(stderr, "Files starting with '-' should be sizes for randomly created input\n");
			exit(1);
		}
        	fp = NULL;
		MOA_Seed(time(0));
        }

	newsize = size;
	
	/* Find new size by determining next closest multiple */
	if (packetsize != 0) {
		if (size%(k*w*packetsize*sizeof(long)) != 0) {
			while (newsize%(k*w*packetsize*sizeof(long)) != 0) 
				newsize++;
		}
	}
	else {
		if (size%(k*w*sizeof(long)) != 0) {
			while (newsize%(k*w*sizeof(long)) != 0) 
				newsize++;
		}
	}
	
	if (buffersize != 0) {
		while (newsize%buffersize != 0) {
			newsize++;
		}
	}


	/* Determine size of k+m files */
	
	stripe_size = newsize/M;
	blocksize= stripe_size/k;
        printf("size:%d\n", size);
        printf("newsize:%d\n",newsize);
	printf("stripe_size:%d\n",stripe_size);	
	printf("blocksize:%d\n", blocksize);

	/* Allow for buffersize and determine number of read-ins */
	if (size > buffersize && buffersize != 0) {
		if (newsize%buffersize != 0) {
			readins = newsize/buffersize;
		}
		else {
			readins = newsize/buffersize;
		}
		block = (char *)malloc(sizeof(char)*buffersize);
		blocksize = buffersize/k;
	}
	else {
		readins = 1;
		buffersize = size;
		block = (char *)malloc(sizeof(char)*newsize);
	}
	printf("blocksize:%d\n", blocksize);

	/* Break inputfile name into the filename and extension */	
	s1 = (char*)malloc(sizeof(char)*(strlen(argv[1])+20));
	s2 = strrchr(argv[1], '/');
	if (s2 != NULL) {
		s2++;
		strcpy(s1, s2);
	}
	else {
		strcpy(s1, argv[1]);
	}
	s2 = strchr(s1, '.');
	if (s2 != NULL) {
          extension = strdup(s2);
          *s2 = '\0';
	} else {
          extension = strdup("");
        }
	
	/* Allocate for full file name */
	fname = (char*)malloc(sizeof(char)*(strlen(argv[1])+strlen(curdir)+20));
	sprintf(temp, "%d", k);
	md = strlen(temp);
	
	/* Allocate data and coding */
	data = (char **)malloc(sizeof(char*)*k);
	coding = (char **)malloc(sizeof(char*)*m);
	for (i = 0; i < m; i++) {
		coding[i] = (char *)malloc(sizeof(char)*blocksize);
                if (coding[i] == NULL) { perror("malloc"); exit(1); }
	}


        fdata = (char **)malloc(sizeof(char*)*M);
            /*for (i = 0; i < M; i++) {
		fdata[i] = (char *)malloc(sizeof(char)*M);
                if (fdata[i] == NULL) { perror("malloc"); exit(1); }
	     }*/
        fcoding = (char **)malloc(sizeof(char*)*M);
            /*for (i = 0; i < M; i++) {
		fcoding[i] = (char *)malloc(sizeof(char)*m*blocksize);
                if (fcoding[i] == NULL) { perror("malloc"); exit(1); }
	    }*/
	
        ffdata = (char **)malloc(sizeof(char*)*M);
            for (i = 0; i < M; i++) {
		ffdata[i] = (char *)malloc(sizeof(char)*k*blocksize);
                if (ffdata[i] == NULL) { perror("malloc"); exit(1); }
	     }
        ccoding = (char **)malloc(sizeof(char*)*M);
            for (i = 0; i < M; i++) {
		ccoding[i] = (char *)malloc(sizeof(char)*m*blocksize);
                if (ccoding[i] == NULL) { perror("malloc"); exit(1); }
	     }

        e = (char *)malloc(sizeof(char)*7);
	
        extra1 = (char *)malloc(sizeof(char)*blocksize);
	extra2 = (char *)malloc(sizeof(char)*blocksize);
        extra3 = (char *)malloc(sizeof(char)*blocksize);

	/* Create coding matrix or bitmatrix and schedule */
	timing_set(&t3);
       switch(tech) {
		case No_Coding:
			break;
		case Reed_Sol_Van:
			matrix = reed_sol_vandermonde_coding_matrix(k, m, w);
			break;
		case Reed_Sol_R6_Op:
			break;
		case Cauchy_Orig:
			matrix = cauchy_original_coding_matrix(k, m, w);
			bitmatrix = jerasure_matrix_to_bitmatrix(k, m, w, matrix);
			schedule = jerasure_smart_bitmatrix_to_schedule(k, m, w, bitmatrix);
			break;
		case Cauchy_Good:
			matrix = cauchy_good_general_coding_matrix(k, m, w);
			bitmatrix = jerasure_matrix_to_bitmatrix(k, m, w, matrix);
			schedule = jerasure_smart_bitmatrix_to_schedule(k, m, w, bitmatrix);
			break;	
		case Liberation:
			bitmatrix = liberation_coding_bitmatrix(k, w);
			schedule = jerasure_smart_bitmatrix_to_schedule(k, m, w, bitmatrix);
			break;
		case Blaum_Roth:
			bitmatrix = blaum_roth_coding_bitmatrix(k, w);
			schedule = jerasure_smart_bitmatrix_to_schedule(k, m, w, bitmatrix);
			break;
		case Liber8tion:
			bitmatrix = liber8tion_coding_bitmatrix(k);
			schedule = jerasure_smart_bitmatrix_to_schedule(k, m, w, bitmatrix);
			break;
		case RDP:
		case EVENODD:
			assert(0);
	  }
	timing_set(&start);
	timing_set(&t4);
	totalsec += timing_delta(&t3, &t4);

	

	/* Read in data until finished */
	n = 1;
	total = 0;

	while (n <= readins) {
		/* Check if padding is needed, if so, add appropriate 
		   number of zeros */
		if (total < size && total+buffersize <= size) {
			total += jfread(block, sizeof(char), buffersize, fp);
		}
		else if (total < size && total+buffersize > size) {
			extra = jfread(block, sizeof(char), buffersize, fp);
			for (i = extra; i < buffersize; i++) {
				block[i] = '0';
			}
		}
		else if (total == size) {
			for (i = 0; i < buffersize; i++) {
				block[i] = '0';
			}
		}

	        /*for(i1=0;i1<k*M;i1++){
			printf("%d ",block[i1]);
	             }
		     printf("\n");*/

		/* Set pointers to point to file data */
		for (i = 0; i < k; i++) {
			data[i] = block+(i*blocksize);
		}
                //printf("data[0]:%p\n",data[0]);
		timing_set(&t3);

      
      //int count=0;
      /* Encode according to coding method */
      for(j=0;j<M;j++){
            fcoding[j] = (char *)malloc(sizeof(char)*m*blocksize);
            fdata[j] = (char *)malloc(sizeof(char)*k*blocksize); 
            for (i = 0; i < k; i++) {
		 data[i] = block+((j*k+i)*blocksize);}
                 //printf("data[0]:%p\n",data[0]);
                 //printf("data[0][0]:%d\n",&data[0][0]);
		switch(tech) {	
			case No_Coding:
				break;
			case Reed_Sol_Van:
				jerasure_matrix_encode(k, m, w, matrix, data, coding, blocksize);
				printf("coding[m-1][blocksize-1]:%d\n",coding[0][blocksize-2]);
                                //printf("coding[0]:%d\n",coding[0]);
                                //printf("coding[1]:%d\n",coding[1]);
				break;
			case Reed_Sol_R6_Op:
				reed_sol_r6_encode(k, w, data, coding, blocksize);
				break;
			case Cauchy_Orig:
				jerasure_schedule_encode(k, m, w, schedule, data, coding, blocksize, packetsize);
				break;
			case Cauchy_Good:
				jerasure_schedule_encode(k, m, w, schedule, data, coding, blocksize, packetsize);
				break;
			case Liberation:
				jerasure_schedule_encode(k, m, w, schedule, data, coding, blocksize, packetsize);
				break;
			case Blaum_Roth:
				jerasure_schedule_encode(k, m, w, schedule, data, coding, blocksize, packetsize);
				break;
			case Liber8tion:
				jerasure_schedule_encode(k, m, w, schedule, data, coding, blocksize, packetsize);
				break;
			case RDP:
			case EVENODD:
				assert(0);
		}
                //printf("w:%d\n",w);
                //printf("Encoding Complete:\n\n");
                //print_data_and_coding(k, m, w, sizeof(long), data, coding);
                //printf("long:%d\n",sizeof(char));

               /*for(i1=0;i1<m;i1++){
                  for(i=0;i<blocksize;i++){
                  fcoding[j][count]=*(coding[i1]+i);
                  count=count+1;
                  }
                }
               count=0;*/
 
             for (i=0;i<m*blocksize;i++)
	     {fcoding[j][i]= *(coding[0]+i);}

             //printf("\n");
             //for(j1=3895;j1<3900;j1++){
             // printf("%d ",fcoding[j][j1]);
             //}

             for(i=0;i<k*blocksize;i++)
             {fdata[j][i] = *(block+j*k*blocksize+i);}   

      }
 
      /*transformation*/
      //k=0,1
        for(i=0;i<M;i++){
            for(j=0;j<k*blocksize;j++){
              ffdata[i][j]=fdata[i][j];
            }
        }
        for(i=0;i<M;i++){
            for(j=0;j<m*blocksize;j++){
              ccoding[i][j]=fcoding[i][j];
            }
        }

        for(i=0;i<7;i++){
               e[0]=20; e[1]=18;e[2]=17;e[3]=16;e[4]=15;e[5]=13;e[6]=167;}
        for(j=0;j<7;j++)
               {printf("%d ",e[j]);}
	       printf("\n");

        /*printf("fdata_c4_8/c0_9\n");
        printf("%p\n ",&fdata[0][0]);
        for(j=0;j<M;j++){
            printf("%d ",fdata[5][j+8*blocksize]);}
            printf("\n");   
        for(j=0;j<M;j++){
            printf("%d ",fdata[1][j+9*blocksize]);}
            printf("\n"); 

        printf("backup_ffdata_c4_8/c0_9\n");
        printf("%p\n ",&ffdata[0][0]);
        for(j=0;j<M;j++){
            printf("%d ",ffdata[5][j+8*blocksize]);}
            printf("\n");
        for(j=0;j<M;j++){
            printf("%d ",ffdata[1][j+9*blocksize]);}
            printf("\n"); */
 
        /*printf("cdata_c5_0/c1_1\n");
        printf("%p\n ",fcoding);
        printf("%p\n ",coding);
        for(j=0;j<M;j++){
            printf("%d ",fcoding[5][j+2*blocksize]);}
            printf("\n");   
        for(j=0;j<M;j++){
            printf("%d ",fcoding[1][j+3*blocksize]);}
            printf("\n"); 

        printf("backup_cdata_c5_2/c1_3\n");
        printf("%p\n ",ccoding);
        for(j=0;j<M;j++){
            printf("%d ",ccoding[5][j+2*blocksize]);}
            printf("\n");   
        for(j=0;j<M;j++){
            printf("%d ",ccoding[1][j+3*blocksize]);}
            printf("\n");*/


        /*for(i1=0;i1<blocksize;i1++){
           galois_region_xor(fdata[3]+i1,fdata[2]+blocksize+i1,1);;
	     	   }*/
        
        /*galois_w08_region_multiply((ffdata[2]+1*blocksize),e[0],blocksize,(ffdata[2]+1*blocksize), 0);
        for(i1=0;i1<blocksize;i1++){
           galois_region_xor(ffdata[2]+1*blocksize+i1,fdata[3]+i1, 1);}

         printf("mul\n");
        for(j=0;j<M;j++){
            printf("%d ",fdata[2][j+blocksize]);}
            printf("\n");   
         for(j=0;j<M;j++){
            printf("%d ",fdata[3][j]);}
            printf("\n"); 
 
        for(j=0;j<M;j++){
            printf("%d ",ffdata[2][j+blocksize]);}
            printf("\n"); 
        for(j=0;j<M;j++){
            printf("%d ",ffdata[3][j]);}
            printf("\n"); */

        //k=0,1
        for(i=0;i<M;i++){
           for(j=0;j<2;j++){
               if(j%2!=0 &&  i%2==0) { 
                 for(i1=0;i1<blocksize;i1++){
		   galois_region_xor(fdata[i+1]+(j-1)*blocksize+i1,fdata[i]+j*blocksize+i1,1);
	     	   }
	        }
               if(j%2==0 && i%2!=0){ 
                   galois_w08_region_multiply((ffdata[i-1]+(j+1)*blocksize),e[j/2],blocksize,(ffdata[i-1]+(j+1)*blocksize), 0);
                   for(i1=0;i1<blocksize;i1++){
		   galois_region_xor(ffdata[i-1]+(j+1)*blocksize+i1,fdata[i]+j*blocksize+i1, 1);
		   }
               }
           }
        } 
        //k=2,3,4,5,6,7
        for(i=0;i<M;i++){
           for(j=2;j<8;j++){
               if(j%2!=0 && (i/2==0 || i/2==2)) { 
                 for(i1=0;i1<blocksize;i1++){
		   galois_region_xor(fdata[i+2]+(j-1)*blocksize+i1,fdata[i]+j*blocksize+i1,1);
	     	   }
	        }
              if(j%2==0 && (i/2==1 || i/2==3)){ 
                   galois_w08_region_multiply((ffdata[i-2]+(j+1)*blocksize),e[j/2],blocksize,(ffdata[i-2]+(j+1)*blocksize), 0);
                   for(i1=0;i1<blocksize;i1++){
		   galois_region_xor(ffdata[i-2]+(j+1)*blocksize+i1,fdata[i]+j*blocksize+i1, 1);
		   }
               }
           }
        } 
        
        //k=8/9
        for(i=0;i<M;i++){
           for(j=8;j<10;j++){
              if(j%2!=0 && i/4==0){ 
                 for(i1=0;i1<blocksize;i1++){
		   galois_region_xor(fdata[i+4]+(j-1)*blocksize+i1,fdata[i]+j*blocksize+i1,1);
	     	   }
	        }
              if(j%2==0 && i/4==1){ 
                   galois_w08_region_multiply((ffdata[i-4]+(j+1)*blocksize),e[j/2],blocksize,(ffdata[i-4]+(j+1)*blocksize), 0);
                   for(i1=0;i1<blocksize;i1++){
		   galois_region_xor(ffdata[i-4]+(j+1)*blocksize+i1,fdata[i]+j*blocksize+i1, 1);
		   }
               }
           }
        } 

        //k=10/11/12/13
        for(i=0;i<M;i++){
           for(j=0;j<4;j++){
              if(j%2!=0 && i/4==0){ 
                 for(i1=0;i1<blocksize;i1++){
		   galois_region_xor(fcoding[i+4]+(j-1)*blocksize+i1,fcoding[i]+j*blocksize+i1,1);
	     	   }
	        }
              if(j%2==0 && i/4==1){ 
                   galois_w08_region_multiply((ccoding[i-4]+(j+1)*blocksize),e[j/2],blocksize,(ccoding[i-4]+(j+1)*blocksize), 0);
                   for(i1=0;i1<blocksize;i1++){
		   galois_region_xor(ccoding[i-4]+(j+1)*blocksize+i1,fcoding[i]+j*blocksize+i1, 1);
		   }
               }
           }
        } 
        
        /*printf("transformation_fdata_c4_8/c0_9\n");
        printf("%p\n ",&fdata[0][0]);
        for(j=0;j<M;j++){
            printf("%d ",fdata[5][j+8*blocksize]);}
            printf("\n");   
        for(j=0;j<M;j++){
            printf("%d ",fdata[1][j+9*blocksize]);}
            printf("\n"); 

        printf("backup_ffdata_c4_8/c0_9\n");
        printf("%p\n ",&ffdata[0][0]);
        for(j=0;j<M;j++){
            printf("%d ",ffdata[5][j+8*blocksize]);}
            printf("\n");
        for(j=0;j<M;j++){
            printf("%d ",ffdata[1][j+9*blocksize]);}
            printf("\n"); */

        printf("transformation_cdata_c5_0/c1_1\n");
        for(j=0;j<M;j++){
            printf("%d ",fcoding[5][j+2*blocksize]);}
            printf("\n");   
        for(j=0;j<M;j++){
            printf("%d ",fcoding[1][j+3*blocksize]);}
            printf("\n"); 

        printf("transformation_backup_cdata_c5_0/c1_1\n");
        printf("%p\n ",ccoding);
        for(j=0;j<M;j++){
            printf("%d ",ccoding[5][j+2*blocksize]);}
            printf("\n");   
        for(j=0;j<M;j++){
            printf("%d ",ccoding[1][j+3*blocksize]);}
            printf("\n"); 

        /*printf("transformation_backup_ffdata_c2_1/c3_0\n");
        printf("%p ",&ffdata[0][0]);
        for(j=0;j<M;j++){
            printf("%d ",ffdata[2][j+blocksize]);}
            printf("\n");
        for(j=0;j<M;j++){
            printf("%d ",ffdata[3][j]);}
            printf("\n"); 
       timing_set(&t4);*/
            
   //test fcoding ccoding
                  /*printf("\n");
                    printf("fcoding:");
		    for(i1=0;i1<M;i1++){
			for(j1=0;j1<m;j1++){
			   printf("%d ",fcoding[i1][j1]);
			}
		           printf("\n");
		     } 

		    printf("\n");
                    printf("fdata:\n");
                    for(i1=0;i1<M;i1++){
	               for(j1=0;j1<k;j1++){
                          printf("%d ",fdata[i1][j1]);
		       }
                            printf("\n");
                    } */              
                                
   //test extra1\extra2\xor function 
                   /*printf("\n");
                   printf("Reference of transformation_C01_C10:\n");
                   for(j=0;j<M;j++){
                      printf("%d ",fdata[2][blocksize+j]);}
                   printf("\n");
                        
                   for(j=0;j<M;j++){
                      printf("%d ",fdata[3][j]);}
	           printf("\n");

                   printf("\n");
                   printf("Two-dimensional to one bit transfer storage\n");
                   for(i1=0;i1<blocksize;i1++){
                        extra1[i1]=fdata[2][blocksize+i1];
                        extra2[i1]=fdata[3][i1];            
                   }   
    
                   for(j=0;j<M;j++)
                   {printf("%d ",extra1[j]);}
	           printf("\n");
                   for(j=0;j<M;j++)
                   {printf("%d ",extra2[j]);}
	           printf("\n");

                   for(i1=0;i1<blocksize;i1++){
                   //galois_region_xor(extra1+i1,extra2+i1,1);
                   galois_region_xor(fdata[2]+blocksize+i1,fdata[3]+i1,1);
                   }
                   printf("after xor(extra2+extra1):\n");
                   for(j=0;j<M;j++)
                   {printf("%d ",extra1[j]);}
	           printf("\n");

                   for(j=0;j<M;j++)
                   {printf("%d ",extra2[j]);}
	           printf("\n");

                   for(j=0;j<M;j++){
                      printf("%d ",fdata[2][blocksize+j]);}
                   printf("\n");
                        
                   for(j=0;j<M;j++){
                      printf("%d ",fdata[3][j]);}
	           printf("\n");*/

 //test e\mul function 
                /*for(i=0;i<7;i++){
                   e[0]=20; e[1]=18;e[2]=17;e[3]=16;e[4]=15;e[5]=13;e[6]=167;}
                for(j=0;j<7;j++)
                   {printf("%d ",e[j]);}
	           printf("\n");
               
               

                printf("before mul\n");
                for(j=0;j<M;j++){
                      printf("%d ",fdata[2][blocksize+j]);}
                   printf("\n");
                for(j=0;j<M;j++){
                      printf("%d ",fdata[3][j]);}
                   printf("\n");
                galois_w08_region_multiply(fdata[2]+blocksize,2,blocksize,fdata[3], 0);    
                printf("after mul(fdata[0]+blocksize,extra3):\n");
                for(j=0;j<M;j++)
                   {printf("%d ",fdata[2][blocksize+j]);}
	           printf("\n");
                for(j=0;j<M;j++){
                      printf("%d ",fdata[3][j]);}
                   printf("\n");*/
//test The backup
            /*for(i=0;i<M;i++){
               for(j=0;j<k*blocksize;j++){
               ffdata[i][j]=fdata[i][j];
               }
            }
            printf("%d ",ffdata[0][0]);
            printf("%d ",fdata[0][0]);
            printf("%d ",&ffdata[0][0]);
            printf("%d ",&fdata[0][0]);*/
//test  region_multiply/xor/w8_xor
         char **a;
         char **b;
         int *c;
         a = (char **)malloc(sizeof(char*)*2);
         for (i = 0; i < 2; i++) {
		a[i] = (char *)malloc(sizeof(char)*3);
                if (a[i] == NULL) { perror("malloc"); exit(1); }
	 }
        b = (char **)malloc(sizeof(char*)*2);
        for (i = 0; i < 2; i++) {
		b[i] = (char *)malloc(sizeof(char)*3);
                if (b[i] == NULL) { perror("malloc"); exit(1); }
	}
        c = (char *)malloc(sizeof(char)*3);

        a[0][0]=1;a[0][1]=2;a[0][2]=3;
        a[1][0]=1;a[1][1]=1;a[1][2]=2;

        c[0]=1;c[1]=4;c[2]=3;
        
       //galois_region_xor(a[0],a[1],3);
       galois_w8_region_xor(a[0],a[1],3);
       for(i1=0;i1<2;i1++){
            for(j=0;j<3;j++){
            printf("%d ",a[i1][j]);
           }
          printf("\n");
       }

      /*for(i=0;i<3;i++){
        galois_w08_region_multiply(a[0],c[i],3,b[0],0);
        galois_w08_region_multiply(a[1],c[i],3,b[1],0);
          for(i1=0;i1<2;i1++){
            for(j=0;j<3;j++){
            printf("%d ",b[i1][j]);
           }
          }
         printf("\n");
        }*/
		/* Write data and encoded data to k+m files */
		for	(i = 1; i <= k; i++) {
			if (fp == NULL) {
				bzero(data[i-1], blocksize);
 			} else {
				sprintf(fname, "%s/Coding/%s_k%0*d%s", curdir, s1, md, i, extension);
				if (n == 1) {
					fp2 = fopen(fname, "wb");
				}
				else {
					fp2 = fopen(fname, "ab");
				}
				fwrite(data[i-1], sizeof(char), blocksize, fp2);
				fclose(fp2);
			}
			
		}
		for	(i = 1; i <= m; i++) {
			if (fp == NULL) {
				bzero(data[i-1], blocksize);
 			} else {
				sprintf(fname, "%s/Coding/%s_m%0*d%s", curdir, s1, md, i, extension);
				if (n == 1) {
					fp2 = fopen(fname, "wb");
				}
				else {
					fp2 = fopen(fname, "ab");
				}
				fwrite(coding[i-1], sizeof(char), blocksize, fp2);
				fclose(fp2);
			}
		}
		n++;
		/* Calculate encoding time */
		totalsec += timing_delta(&t3, &t4);
	}

	/* Create metadata file */
        if (fp != NULL) {
		sprintf(fname, "%s/Coding/%s_meta.txt", curdir, s1);
		fp2 = fopen(fname, "wb");
		fprintf(fp2, "%s\n", argv[1]);
		fprintf(fp2, "%d\n", size);
		fprintf(fp2, "%d %d %d %d %d\n", k, m, w, packetsize, buffersize);
		fprintf(fp2, "%s\n", argv[4]);
		fprintf(fp2, "%d\n", tech);
		fprintf(fp2, "%d\n", readins);
		fclose(fp2);
	}


	/* Free allocated memory */
	free(s1);
	free(fname);
	free(block);
	free(curdir);
	
	/* Calculate rate in MB/sec and print */
	timing_set(&t2);
	tsec = timing_delta(&t1, &t2);
	printf("Encoding (MB/sec): %0.10f\n", (((double) size)/1024.0/1024.0)/totalsec);
	printf("En_Total (MB/sec): %0.10f\n", (((double) size)/1024.0/1024.0)/tsec);

	return 0;
}

/* is_prime returns 1 if number if prime, 0 if not prime */
int is_prime(int w) {
	int prime55[] = {2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,
	    73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,
		    181,191,193,197,199,211,223,227,229,233,239,241,251,257};
	int i;
	for (i = 0; i < 55; i++) {
		if (w%prime55[i] == 0) {
			if (w == prime55[i]) return 1;
			else { return 0; }
		}
	}
	assert(0);
}

/* Handles ctrl-\ event */
void ctrl_bs_handler(int dummy) {
	time_t mytime;
	mytime = time(0);
	fprintf(stderr, "\n%s\n", ctime(&mytime));
	fprintf(stderr, "You just typed ctrl-\\ in encoder.c.\n");
	fprintf(stderr, "Total number of read ins = %d\n", readins);
	fprintf(stderr, "Current read in: %d\n", n);
	fprintf(stderr, "Method: %s\n\n", Methods[method]);	
	signal(SIGQUIT, ctrl_bs_handler);
}

