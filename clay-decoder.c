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
technique, w, and packetsize.  It is the companion program
of encoder.c, which creates k+m files.  This program assumes 
that up to m erasures have occurred in the k+m files.  It
reads in the k+m files or marks the file as erased. It then
recreates the original file and creates a new file with the
suffix "decoded" with the decoded contents of the file.

This program does not error check command line arguments because 
it is assumed that encoder.c has been called previously with the
same arguments, and encoder.c does error check.
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <assert.h>
#include <unistd.h>
#include <sys/time.h>
#include <sys/stat.h>
#include <signal.h>
#include <unistd.h>
#include "jerasure.h"
#include "reed_sol.h"
#include "galois.h"
#include "cauchy.h"
#include "liberation.h"
#include "timing.h"

#define N 10
#define M 128

enum Coding_Technique {Reed_Sol_Van, Reed_Sol_R6_Op, Cauchy_Orig, Cauchy_Good, Liberation, Blaum_Roth, Liber8tion, RDP, EVENODD, No_Coding};

char *Methods[N] = {"reed_sol_van", "reed_sol_r6_op", "cauchy_orig", "cauchy_good", "liberation", "blaum_roth", "liber8tion", "rdp", "evenodd", "no_coding"};

/* Global variables for signal handler */
enum Coding_Technique method;
int readins, n;

/* Function prototype */
void ctrl_bs_handler(int dummy);

int main (int argc, char **argv) {
	FILE *fp;				// File pointer

	/* Jerasure arguments */
	char **data;
	char **coding;
        char **pdata;
        char **pcoding;
        
        char **fdata;           
        char **fcoding;         
        char **ffdata;           //backup
        char **ccoding;         //backup
        char *e;
        char *e1;

	int *erasures;
	int *erased;
	int *matrix;
	int *bitmatrix;
	
	/* Parameters */
	int k, m, w, packetsize, buffersize;
	int tech;
	char *c_tech;
	
	int i, j,i1,j1;				// loop control variable, s
	int blocksize = 0;			// size of individual files
	int origsize;			// size of file before padding
	int total;				// used to write data, not padding to file
	struct stat status;		// used to find size of individual files
	int numerased;			// number of erased files
        int Bsize;
        Bsize=512000;
		
	/* Used to recreate file names */
	char *temp;
	char *cs1, *cs2, *extension;
	char *fname;
	int md;
	char *curdir;

	/* Used to time decoding */
	struct timing t1, t2, t3, t4, t5, t6;
	double tsec;
	double totalsec;
        double transec;

	
	signal(SIGQUIT, ctrl_bs_handler);

	matrix = NULL;
	bitmatrix = NULL;
	totalsec = 0.0;
	
	/* Start timing */
	timing_set(&t1);

	/* Error checking parameters */
	if (argc != 2) {
		fprintf(stderr, "usage: inputfile\n");
		exit(0);
	}
	curdir = (char *)malloc(sizeof(char)*1000);
	assert(curdir == getcwd(curdir, 1000));
	
	/* Begin recreation of file names */
	cs1 = (char*)malloc(sizeof(char)*strlen(argv[1]));
	cs2 = strrchr(argv[1], '/');
	if (cs2 != NULL) {
		cs2++;
		strcpy(cs1, cs2);
	}
	else {
		strcpy(cs1, argv[1]);
	}
	cs2 = strchr(cs1, '.');
	if (cs2 != NULL) {
                extension = strdup(cs2);
		*cs2 = '\0';
	} else {
           extension = strdup("");
        }	
	fname = (char *)malloc(sizeof(char*)*(100+strlen(argv[1])+20));

	/* Read in parameters from metadata file */
	sprintf(fname, "%s/Coding/%s_meta.txt", curdir, cs1);

	fp = fopen(fname, "rb");
        if (fp == NULL) {
          fprintf(stderr, "Error: no metadata file %s\n", fname);
          exit(1);
        }
	temp = (char *)malloc(sizeof(char)*(strlen(argv[1])+20));
	if (fscanf(fp, "%s", temp) != 1) {
		fprintf(stderr, "Metadata file - bad format\n");
		exit(0);
	}
	
	if (fscanf(fp, "%d", &origsize) != 1) {
		fprintf(stderr, "Original size is not valid\n");
		exit(0);
	}
	if (fscanf(fp, "%d %d %d %d %d", &k, &m, &w, &packetsize, &buffersize) != 5) {
		fprintf(stderr, "Parameters are not correct\n");
		exit(0);
	}
	c_tech = (char *)malloc(sizeof(char)*(strlen(argv[1])+20));
	if (fscanf(fp, "%s", c_tech) != 1) {
		fprintf(stderr, "Metadata file - bad format\n");
		exit(0);
	}
	if (fscanf(fp, "%d", &tech) != 1) {
		fprintf(stderr, "Metadata file - bad format\n");
		exit(0);
	}
	method = tech;
	if (fscanf(fp, "%d", &readins) != 1) {
		fprintf(stderr, "Metadata file - bad format\n");
		exit(0);
	}
	fclose(fp);	
 
        printf("origsize:%d\n",origsize);
        //printf("packetsize:%d\n",packetsize);
        printf("buffersize:%d\n",buffersize);
         
	/* Allocate memory */
	erased = (int *)malloc(sizeof(int)*(k+m));
	for (i = 0; i < k+m; i++)
		erased[i] = 0;
	erasures = (int *)malloc(sizeof(int)*(k+m));

	data = (char **)malloc(sizeof(char *)*M);
	coding = (char **)malloc(sizeof(char *)*M);

        pdata = (char **)malloc(sizeof(char*)*k);
            for(j=0;j<k;j++){
               pdata[j] = (char *)malloc(sizeof(char)*Bsize);}

        pcoding = (char **)malloc(sizeof(char*)*m);
            for (i = 0; i < m; i++) {
		pcoding[i] = (char *)malloc(sizeof(char)*Bsize);
                if (pcoding[i] == NULL) { perror("malloc"); exit(1); }
	     }

        fdata = (char **)malloc(sizeof(char*)*M);
            for(j=0;j<M;j++){
               fdata[j] = (char *)malloc(sizeof(char)*k*Bsize);}

        fcoding = (char **)malloc(sizeof(char*)*M);
            for (i = 0; i < M; i++) {
		fcoding[i] = (char *)malloc(sizeof(char)*m*Bsize);
                if (fcoding[i] == NULL) { perror("malloc"); exit(1); }
	     }
        ffdata = (char **)malloc(sizeof(char*)*M);
            for(j=0;j<M;j++){
               ffdata[j] = (char *)malloc(sizeof(char)*k*Bsize);}

        ccoding = (char **)malloc(sizeof(char*)*M);
            for (i = 0; i < M; i++) {
		ccoding[i] = (char *)malloc(sizeof(char)*m*Bsize);
                if (ccoding[i] == NULL) { perror("malloc"); exit(1); }
	     }

	if (buffersize != origsize) {
		for (i = 0; i < M; i++) {
			data[i] = (char *)malloc(sizeof(char)*(buffersize/k/M));
		}
		for (i = 0; i < m; i++) {
			coding[i] = (char *)malloc(sizeof(char)*(buffersize/M/m));
		}
		blocksize = buffersize/k/M;
	}
        e=(char *)malloc(sizeof(char)*7);
        e1=(char *)malloc(sizeof(char)*7);

        printf("buffersize2:%d\n ",buffersize);
        printf("blocksize:%d\n",blocksize);
        printf("readins:%d\n", readins);
	sprintf(temp, "%d", k);

	md = strlen(temp);
	timing_set(&t3);
	/* Create coding matrix or bitmatrix */
	switch(tech) {
		case No_Coding:
			break;
		case Reed_Sol_Van:
			matrix = reed_sol_vandermonde_coding_matrix(k, m, w);
			break;
		case Reed_Sol_R6_Op:
			matrix = reed_sol_r6_coding_matrix(k, w);
			break;
		case Cauchy_Orig:
			matrix = cauchy_original_coding_matrix(k, m, w);
			bitmatrix = jerasure_matrix_to_bitmatrix(k, m, w, matrix);
			break;
		case Cauchy_Good:
			matrix = cauchy_good_general_coding_matrix(k, m, w);
			bitmatrix = jerasure_matrix_to_bitmatrix(k, m, w, matrix);
			break;
		case Liberation:
			bitmatrix = liberation_coding_bitmatrix(k, w);
			break;
		case Blaum_Roth:
			bitmatrix = blaum_roth_coding_bitmatrix(k, w);
			break;
		case Liber8tion:
			bitmatrix = liber8tion_coding_bitmatrix(k);
	}
	timing_set(&t4);
	totalsec += timing_delta(&t3, &t4);
	
        
	/* Begin decoding process */
	total = 0;
	n = 1;	
	while (n <= readins) {
		numerased = 0;
		/* Open files, check for erasures, read in data/coding */	
		for (i = 1; i <= k; i++) {
			sprintf(fname, "%s/Coding/%s_k%0*d%s", curdir, cs1, md, i, extension);
			fp = fopen(fname, "rb");
			if (fp == NULL) {
				erased[i-1] = 1;
				erasures[numerased] = i-1;
				numerased++;
				printf("%s failed\n", fname);
			}
			else {
                               /*fread(fdata[i],sizeof(char),blocksize,fp);
                               printf("data_readtest\n");
                               for(j=0;j<blocksize;j++)
                               {printf("%d ",fdata[3][j]);}*/
				if (buffersize == origsize) {
					stat(fname, &status);
					blocksize = status.st_size/M;
                                        //printf("%d ",blocksize);

                                        for(j=0;j<M;j++){
                                           data[j] = (char *)malloc(sizeof(char)*blocksize);
					   assert(blocksize == fread(data[j], sizeof(char), blocksize, fp));
                                        }
				}
				else {
					fseek(fp, blocksize*(n-1), SEEK_SET); 
                                        for(j=0;j<M;j++){
					assert(blocksize == fread(data[j], sizeof(char), blocksize, fp));}
				}
				fclose(fp);

                               for(j=0;j<M;j++){
                                 for(j1=0;j1<blocksize;j1++){
                                    fdata[j][(i-1)*blocksize+j1]=data[j][j1];
                                 }
                              }
	              }
                       
		}
                
		for (i = 1; i <= m; i++) {
			sprintf(fname, "%s/Coding/%s_m%0*d%s", curdir, cs1, md, i, extension);
				fp = fopen(fname, "rb");
			if (fp == NULL) {
				erased[k+(i-1)] = 1;
				erasures[numerased] = k+i-1;
				numerased++;
				printf("%s failed\n", fname);
			}
			else {
				if (buffersize == origsize) {
					stat(fname, &status);
					blocksize = status.st_size/M;
                                        //printf("%d ",blocksize);
                                        for(j=0;j<M;j++){
					coding[j] = (char *)malloc(sizeof(char)*blocksize);
					assert(blocksize == fread(coding[j], sizeof(char), blocksize, fp));}
				}
				else {
					fseek(fp, blocksize*(n-1), SEEK_SET);
                                        for(j=0;j<M;j++){
					assert(blocksize == fread(coding[j], sizeof(char), blocksize, fp));}
				}	
				fclose(fp);
                              for(j=0;j<M;j++){
                                 for(j1=0;j1<blocksize;j1++){
                                    fcoding[j][(i-1)*blocksize+j1]=coding[j][j1];
                                 }
                              }
			}
		}
                          
		/* Finish allocating data/coding if needed */
		/*if (n == 1) {
			for (i = 0; i < numerased; i++) {
				if (erasures[i] < k) {
                                        for(j=0;j<M;j++){
					data[j]= (char *)malloc(sizeof(char)*k*blocksize);}
				}
				else {
                                        for(j=0;j<M;j++){
					coding[j] = (char *)malloc(sizeof(char)*m*blocksize);}
				}
			}
		}*/
		erasures[numerased] = -1;

      timing_set(&t5);  
      /* invert transformation*/
      for(i=0;i<7;i++){
               e[0]=20; e[1]=18;e[2]=21;e[3]=16;e[4]=25;e[5]=13;e[6]=54;}   
      for(i=0;i<7;i++){
               e1[0]=1; e1[1]=1;e1[2]=1;e1[3]=1;e1[4]=1;e1[5]=1;e1[6]=1;}
      galois_region_xor(e,e1,7);
      
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

     /*
        //k=0,1
        for(i=0;i<M;i++){
           for(j=0;j<2;j++){
             if(erased[j]==0){
               if(j%2!=0 &&  i%2==0) {                                                                 //C1_2+C2_1 xor C1_2e1+c2_1 to C1_2(1+e1)
		   galois_region_xor(fdata[i+1]+(j-1)*blocksize,fdata[i]+j*blocksize,blocksize);
                   galois_w08_region_multiply(fdata[i]+j*blocksize,galois_single_divide(1,e1[j/2],w),blocksize,fdata[i]+j*blocksize,0); 
	       }
               if(j%2==0 && i%2!=0){ 
                   galois_w08_region_multiply((fdata[i-1]+(j+1)*blocksize),e[j/2],blocksize,(ffdata[i-1]+(j+1)*blocksize), 0);
		   galois_region_xor(ffdata[i-1]+(j+1)*blocksize,fdata[i]+j*blocksize, blocksize);
               }
             }
           }
        } 

       //k=2,3,4,5,6,7
       for(i=0;i<M;i++){
           for(j=2;j<8;j++){
               if(j%2!=0 && (i/2==0 || i/2==2) && erased[j]==0 && erased[j-1]==0) {                                                                 
		   galois_region_xor(fdata[i+2]+(j-1)*blocksize,fdata[i]+j*blocksize,blocksize);
                   galois_w08_region_multiply(fdata[i]+j*blocksize,galois_single_divide(1,e1[j/2],w),blocksize,fdata[i]+j*blocksize,0); 
	       }
               if(j%2==0 && (i/2==1 || i/2==3) && erased[j]==0 && erased[j+1]==0){ 
                   galois_w08_region_multiply((fdata[i-2]+(j+1)*blocksize),e[j/2],blocksize,(ffdata[i-2]+(j+1)*blocksize), 0);
		   galois_region_xor(ffdata[i-2]+(j+1)*blocksize,fdata[i]+j*blocksize, blocksize);
               }
           }
        } 

        //k=8/9
        for(i=0;i<M;i++){
           for(j=8;j<10;j++){
              if(j%2!=0 && i/4==0 && erased[j]==0 && erased[j-1]==0){ 
                 galois_region_xor(fdata[i+4]+(j-1)*blocksize,fdata[i]+j*blocksize,blocksize);
                 galois_w08_region_multiply(fdata[i]+j*blocksize,galois_single_divide(1,e1[j/2],w),blocksize,fdata[i]+j*blocksize,0); 
	        }
              if(j%2==0 && i/4==1 && erased[j]==0 && erased[j+1]==0){ 
                   galois_w08_region_multiply((fdata[i-4]+(j+1)*blocksize),e[j/2],blocksize,(ffdata[i-4]+(j+1)*blocksize), 0);
		   galois_region_xor(ffdata[i-4]+(j+1)*blocksize,fdata[i]+j*blocksize, blocksize);
		 }
           }
        } 

        //k=10/11/12/13 or m=0/1/2/3
        for(i=0;i<M;i++){
           for(j=0;j<4;j++){
              if(j%2!=0 && i/4==0 && erased[k+j]==0 && erased[k+j-1]==0){ 
                 galois_region_xor(fcoding[i+4]+(j-1)*blocksize,fcoding[i]+j*blocksize,blocksize);
                 galois_w08_region_multiply(fcoding[i]+j*blocksize,galois_single_divide(1,e1[4+j/2],w),blocksize,fcoding[i]+j*blocksize,0); 
	      }
              if(j%2==0 && i/4==1 && erased[k+j]==0 && erased[k+j-1]==0){ 
                  galois_w08_region_multiply((fcoding[i-4]+(j+1)*blocksize),e[4+j/2],blocksize,(ccoding[i-4]+(j+1)*blocksize), 0);
		  galois_region_xor(ccoding[i-4]+(j+1)*blocksize,fcoding[i]+j*blocksize, blocksize);
               }
           }
        }  
      */

       //k=0,1
        for(i=0;i<M;i++){
           for(j=0;j<2;j++){
             if(erased[j]==0){
               if(j%2!=0 && i%2==0) {                                                                 //C1_2+2*C2_1 xor C1_2*2+c2_1 to C1_2(1+2)+c2_1(1+2)
		   galois_region_xor(fdata[i+1]+(j-1)*blocksize,fdata[i]+j*blocksize,blocksize);      
                   galois_w08_region_multiply(fdata[i]+j*blocksize,galois_single_divide(1,3,w),blocksize,fdata[i]+j*blocksize,0); 
                   galois_region_xor(fdata[i+1]+(j-1)*blocksize,fdata[i]+j*blocksize,blocksize); 
                   galois_w08_region_multiply(fdata[i]+j*blocksize,galois_single_divide(1,3,w),blocksize,fdata[i]+j*blocksize,0); 
	       }
               if(j%2==0 && i%2!=0){ 
                   galois_w08_region_multiply((fdata[i-1]+(j+1)*blocksize),2,blocksize,(ffdata[i-1]+(j+1)*blocksize), 0);
		   galois_region_xor(ffdata[i-1]+(j+1)*blocksize,fdata[i]+j*blocksize, blocksize);
               }
             }
           }
        } 
       //k=2,3
       for(i=0;i<M;i++){
           i1=i-(i/4)*4;
           for(j=2;j<4;j++){
               if(j%2!=0 && i1<2 && erased[j]==0 && erased[j-1]==0) {                                                                 
		   galois_region_xor(fdata[i+2]+(j-1)*blocksize,fdata[i]+j*blocksize,blocksize);      
                   galois_w08_region_multiply(fdata[i]+j*blocksize,galois_single_divide(1,3,w),blocksize,fdata[i]+j*blocksize,0); 
                   galois_region_xor(fdata[i+2]+(j-1)*blocksize,fdata[i]+j*blocksize,blocksize); 
                   galois_w08_region_multiply(fdata[i]+j*blocksize,galois_single_divide(1,3,w),blocksize,fdata[i]+j*blocksize,0);
	       }
               if(j%2==0 && i1>=2 && erased[j]==0 && erased[j+1]==0){ 
                   galois_w08_region_multiply((fdata[i-2]+(j+1)*blocksize),2,blocksize,(ffdata[i-2]+(j+1)*blocksize), 0);
		   galois_region_xor(ffdata[i-2]+(j+1)*blocksize,fdata[i]+j*blocksize, blocksize);
               }
           }
        } 

       //k=4,5
       for(i=0;i<M;i++){
           i1=i-(i/8)*8;
           for(j=4;j<6;j++){
               if(j%2!=0 && i1<4 && erased[j]==0 && erased[j-1]==0) {                                                                 
		   galois_region_xor(fdata[i+4]+(j-1)*blocksize,fdata[i]+j*blocksize,blocksize);      
                   galois_w08_region_multiply(fdata[i]+j*blocksize,galois_single_divide(1,3,w),blocksize,fdata[i]+j*blocksize,0); 
                   galois_region_xor(fdata[i+4]+(j-1)*blocksize,fdata[i]+j*blocksize,blocksize); 
                   galois_w08_region_multiply(fdata[i]+j*blocksize,galois_single_divide(1,3,w),blocksize,fdata[i]+j*blocksize,0);
	       }
               if(j%2==0 && i1>=4 && erased[j]==0 && erased[j+1]==0){ 
                   galois_w08_region_multiply((fdata[i-4]+(j+1)*blocksize),2,blocksize,(ffdata[i-4]+(j+1)*blocksize), 0);
		   galois_region_xor(ffdata[i-4]+(j+1)*blocksize,fdata[i]+j*blocksize, blocksize);
               }
           }
        } 
      
       //k=6,7
       for(i=0;i<M;i++){
           i1=i-(i/16)*16;
           for(j=6;j<8;j++){
               if(j%2!=0 && i1<8 && erased[j]==0 && erased[j-1]==0) {                                                                 
		   galois_region_xor(fdata[i+8]+(j-1)*blocksize,fdata[i]+j*blocksize,blocksize);      
                   galois_w08_region_multiply(fdata[i]+j*blocksize,galois_single_divide(1,3,w),blocksize,fdata[i]+j*blocksize,0); 
                   galois_region_xor(fdata[i+8]+(j-1)*blocksize,fdata[i]+j*blocksize,blocksize); 
                   galois_w08_region_multiply(fdata[i]+j*blocksize,galois_single_divide(1,3,w),blocksize,fdata[i]+j*blocksize,0);
	       }
               if(j%2==0 && i1>=8 && erased[j]==0 && erased[j+1]==0){ 
                   galois_w08_region_multiply((fdata[i-8]+(j+1)*blocksize),2,blocksize,(ffdata[i-8]+(j+1)*blocksize), 0);
		   galois_region_xor(ffdata[i-8]+(j+1)*blocksize,fdata[i]+j*blocksize, blocksize);
               }
           }
        }

        //k=8,9
       for(i=0;i<M;i++){
           i1=i-(i/32)*32;
           for(j=8;j<10;j++){
               if(j%2!=0 && i1<16 && erased[j]==0 && erased[j-1]==0) {                                                                 
		   galois_region_xor(fdata[i+16]+(j-1)*blocksize,fdata[i]+j*blocksize,blocksize);      
                   galois_w08_region_multiply(fdata[i]+j*blocksize,galois_single_divide(1,3,w),blocksize,fdata[i]+j*blocksize,0); 
                   galois_region_xor(fdata[i+16]+(j-1)*blocksize,fdata[i]+j*blocksize,blocksize); 
                   galois_w08_region_multiply(fdata[i]+j*blocksize,galois_single_divide(1,3,w),blocksize,fdata[i]+j*blocksize,0);
	       } 
               if(j%2==0 && i1>=16 && erased[j]==0 && erased[j+1]==0){ 
                   galois_w08_region_multiply((fdata[i-16]+(j+1)*blocksize),2,blocksize,(ffdata[i-16]+(j+1)*blocksize), 0);
		   galois_region_xor(ffdata[i-16]+(j+1)*blocksize,fdata[i]+j*blocksize, blocksize);
               }
           }
        }

        //k=10/11/12/13 or m=0/1/2/3
         for(i=0;i<M;i++){
           i1=i-(i/64)*64;
           for(j=0;j<2;j++){
              if(j%2!=0 && i1<32 && erased[k+j]==0 && erased[k+j-1]==0){ 
                 galois_region_xor(fcoding[i+32]+(j-1)*blocksize,fcoding[i]+j*blocksize,blocksize);
                 galois_w08_region_multiply(fcoding[i]+j*blocksize,galois_single_divide(1,3,w),blocksize,fcoding[i]+j*blocksize,0);
                 galois_region_xor(fcoding[i+32]+(j-1)*blocksize,fcoding[i]+j*blocksize,blocksize);
                 galois_w08_region_multiply(fcoding[i]+j*blocksize,galois_single_divide(1,3,w),blocksize,fcoding[i]+j*blocksize,0); 
	      }
              if(j%2==0 && i1>=32&& erased[k+j]==0 && erased[k+j-1]==0){ 
                  //printf("%d ",i);
                  //printf("\n");  
                  galois_w08_region_multiply((fcoding[i-32]+(j+1)*blocksize),2,blocksize,(ccoding[i-32]+(j+1)*blocksize), 0);
		  galois_w8_region_xor(ccoding[i-32]+(j+1)*blocksize,fcoding[i]+j*blocksize, blocksize);
                  
               }
           }
        } 
      
        for(i=0;i<M;i++){
           i1=i-(i/128)*128;
           for(j=2;j<4;j++){
              if(j%2!=0 && i1<64 && erased[k+j]==0 && erased[k+j-1]==0){ 
                 galois_region_xor(fcoding[i+64]+(j-1)*blocksize,fcoding[i]+j*blocksize,blocksize);
                 galois_w08_region_multiply(fcoding[i]+j*blocksize,galois_single_divide(1,3,w),blocksize,fcoding[i]+j*blocksize,0);
                 galois_region_xor(fcoding[i+64]+(j-1)*blocksize,fcoding[i]+j*blocksize,blocksize);
                 galois_w08_region_multiply(fcoding[i]+j*blocksize,galois_single_divide(1,3,w),blocksize,fcoding[i]+j*blocksize,0); 
	      }
              if(j%2==0 && i1>=64 && erased[k+j]==0 && erased[k+j-1]==0){ 
                  galois_w08_region_multiply((fcoding[i-64]+(j+1)*blocksize),2,blocksize,(ccoding[i-64]+(j+1)*blocksize), 0);
		  galois_region_xor(ccoding[i-64]+(j+1)*blocksize,fcoding[i]+j*blocksize, blocksize);
               }
           }
        }
   timing_set(&t6); 

   timing_set(&t3);
		/* Choose proper decoding method */
		if (tech == Reed_Sol_Van || tech == Reed_Sol_R6_Op) {
                        for(j=0;j<M;j++){
                           for(i1=0;i1<k;i1++){
                              pdata[i1]=fdata[j]+i1*blocksize;}
                              //printf("\n");
                              //printf("%d ",pdata[1][2]);
                           for(i1=0;i1<m;i1++){
                              pcoding[i1]=fcoding[j]+i1*blocksize;}   
			      i = jerasure_matrix_decode(k, m, w, matrix, 1, erasures, pdata, pcoding, blocksize);
                           //printf("\n");
                           //printf("%d \n",i);
                         }
                        
		}
		else if (tech == Cauchy_Orig || tech == Cauchy_Good || tech == Liberation || tech == Blaum_Roth || tech == Liber8tion) {
			i = jerasure_schedule_decode_lazy(k, m, w, bitmatrix, erasures, data, coding, blocksize, packetsize, 1);
		}
		else {
			fprintf(stderr, "Not a valid coding technique.\n");
			exit(0);
		}

     timing_set(&t4);
        
		/* Exit if decoding was unsuccessful */
                //printf("%d \n",i);
		if (i == -1) {
			fprintf(stderr, "Unsuccessful!\n");
			exit(0);
		}
	
		/* Create decoded file */
		sprintf(fname, "%s/Coding/%s_decoded%s", curdir, cs1, extension);
		if (n == 1) {
			fp = fopen(fname, "wb");
		}
		else {
			fp = fopen(fname, "ab");
		}
		for (i = 0; i < M; i++) {
			if (total+k*blocksize <= origsize) {
				{fwrite(fdata[i], sizeof(char), k*blocksize, fp);}
				 total+= k*blocksize;
			}
			else {
				for(j=0;j<10*blocksize;j++){
					if (total < origsize) {  
						fprintf(fp, "%c", fdata[i][j]);
						total++;
					}
					else {
						break;
					}
					
				}
			}
		}
		n++;
		fclose(fp);
		totalsec += timing_delta(&t3, &t4);
	}
	
	/* Free allocated memory */
	free(cs1);
	free(extension);
	free(fname);
	free(data);
	free(coding);
	free(erasures);
	free(erased);
	
	/* Stop timing and print time */
	timing_set(&t2);
        tsec = timing_delta(&t1, &t2);
        transec = timing_delta(&t5, &t6);
        printf("decoding(sec)_mid: %0.10f\n", totalsec);
        printf("decoding(sec)_tran: %0.10f\n", transec);
        totalsec += timing_delta(&t5, &t6);
        printf("decoding(sec)_mid: %0.10f\n", totalsec);
	printf("Decoding (MB/sec): %0.10f\n", (((double) origsize)/1024.0/1024.0)/totalsec);
	printf("De_Total (MB/sec): %0.10f\n\n", (((double) origsize)/1024.0/1024.0)/tsec);

	return 0;
}	

void ctrl_bs_handler(int dummy) {
	time_t mytime;
	mytime = time(0);
	fprintf(stderr, "\n%s\n", ctime(&mytime));
	fprintf(stderr, "You just typed ctrl-\\ in decoder.c\n");
	fprintf(stderr, "Total number of read ins = %d\n", readins);
	fprintf(stderr, "Current read in: %d\n", n);
	fprintf(stderr, "Method: %s\n\n", Methods[method]);
	signal(SIGQUIT, ctrl_bs_handler);
}
