#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <sys/time.h>
#define MSIZE 256
double matrix_a[MSIZE][MSIZE];
double matrix_b[MSIZE][MSIZE];
double matrix_r[MSIZE][MSIZE];

void initialize_matrices()
{
    int i, j;
    for (i = 0; i < MSIZE; i++)
    {
        for (j = 0; j < MSIZE; j++)
        {
            matrix_a[i][j] = (double)rand() / RAND_MAX;
            matrix_b[i][j] = (double)rand() / RAND_MAX;
            matrix_r[i][j] = 0.0;
        }
    }
}

void multiply_matrices()
{
    int i, j, k;
    for (i = 0; i < MSIZE; i++)
    {
        for (j = 0; j < MSIZE; j++)
        {
            for (k = 0; k < MSIZE; k++)
            {
                matrix_r[i][j] += matrix_a[i][k] * matrix_b[k][j];
            }
        }
    }
}

void print_matrix(double matrix[MSIZE][MSIZE])
{
   for (int c = 0; c < MSIZE; c++) {
      for (int d = 0; d < MSIZE; d++)
        printf("%lf\t", matrix[c][d]);
 
      printf("\n");
   }
}

int main(int argc, char *argv[])
{
    int i;
    printf("1. Initializing Matrices \n");
    initialize_matrices();
    // matrix-matrix multiply: this takes most of the time
    // printf("2. Matrix A is: \n");
    // print_matrix(matrix_a);
    // printf("3. Matrix B is: \n");
    // print_matrix(matrix_b);
    multiply_matrices();
    memset(matrix_r, '0', sizeof(double) * MSIZE * MSIZE);
    //Begin timing
    struct timeval time_start;
    gettimeofday(&time_start, NULL);
    multiply_matrices();
    //End timing
    struct timeval time_end;
    gettimeofday(&time_end, NULL);
    unsigned int time_total = (time_end.tv_sec * 1000000 + time_end.tv_usec) - (time_start.tv_sec * 1000000 + time_start.tv_usec); 
    // printf("4. Result Matrix is: \n");
    // print_matrix(matrix_r);
    printf("Matrix multiplication took %fs\n", time_total * 1e-6);
    return 0;
}

