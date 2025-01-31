// Frances Y. Kuo
//
// Email: <f.kuo@unsw.edu.au>
// School of Mathematics and Statistics
// University of New South Wales
// Sydney NSW 2052, Australia
// 
// Last updated: 21 October 2008
//
//   You may incorporate this source code into your own program 
//   provided that you
//   1) acknowledge the copyright owner in your program and publication
//   2) notify the copyright owner by email
//   3) offer feedback regarding your experience with different direction numbers
//
//
// -----------------------------------------------------------------------------
// Licence pertaining to sobol.cc and the accompanying sets of direction numbers
// -----------------------------------------------------------------------------
// Copyright (c) 2008, Frances Y. Kuo and Stephen Joe
// All rights reserved.
// 
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are met:
// 
//     * Redistributions of source code must retain the above copyright
//       notice, this list of conditions and the following disclaimer.
// 
//     * Redistributions in binary form must reproduce the above copyright
//       notice, this list of conditions and the following disclaimer in the
//       documentation and/or other materials provided with the distribution.
// 
//     * Neither the names of the copyright holders nor the names of the
//       University of New South Wales and the University of Waikato
//       and its contributors may be used to endorse or promote products derived
//       from this software without specific prior written permission.
// 
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS ``AS IS'' AND ANY
// EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
// WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
// DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDERS BE LIABLE FOR ANY
// DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
// (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
// LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
// ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
// SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
// -----------------------------------------------------------------------------

#include <algorithm>
#include <cstdlib> // *** Thanks to Leonhard Gruenschloss and Mike Giles   ***
#include <cmath>   // *** for pointing out the change in new g++ compilers ***

#include <iostream>
#include <iomanip>
#include <fstream>

using namespace std;

// ----- SOBOL POINTS GENERATOR BASED ON GRAYCODE ORDER -----------------
// INPUT: 
//   N         number of points  (cannot be greater than 2^32)
//   D         dimension  (make sure that the data file contains enough data!!)      
//   dir_file  the input file containing direction numbers
//
// OUTPUT:
//   A 2-dimensional array POINTS, where
//     
//     POINTS[i][j] = the jth component of the ith point,
//   
//   with i indexed from 0 to N-1 and j indexed from 0 to D-1
//
// ----------------------------------------------------------------------

double **sobol_points(unsigned N,
                      unsigned D,
                      char *dir_file)
{
  ifstream infile(dir_file,ios::in);
  if (!infile)
    {
      cout << "Input file containing direction numbers cannot be found!\n";
      exit(1);
    }
  char buffer[1000];
  infile.getline(buffer,1000,'\n');

  // L = max number of bits needed 
  unsigned L = (unsigned)ceil(log((double)(N + 1))/log(2.0)); 

  // C[i] = index from the right of the first zero bit of i
  unsigned *C = new unsigned [N];
  for (unsigned i = 0; i < N; ++i)
    {
      C[i] = 0;
      unsigned value = i;
      while (value & 1)
        {
          value >>= 1;
          C[i]++;
        }
    }
  
  // POINTS[i][j] = the jth component of the ith point
  //                with i indexed from 0 to D-1 and j indexed from 0 to N-1
  double **POINTS = new double * [D];
  for (unsigned i = 0; i < D; ++i)
    POINTS[i] = new double [N];
  for (unsigned j = 0; j < N; ++j)
    POINTS[0][j] = 0; 

  // ----- Compute the first dimension -----
  
  // Compute direction numbers V[1] to V[L], scaled by pow(2,32)
  unsigned *V = new unsigned [L]; 
  for (unsigned i = 0; i < L; ++i)
    V[i] = 1 << (31 - i); // all m's = 1

  // The factor to divide everything by 2^32.
  const double FACTOR = pow(2.0,32);
  
  unsigned x = 0;
  for (unsigned j = 0; j < N; ++j)
    {
      x ^= V[C[j]];
      POINTS[0][j] = (double)x / FACTOR; // *** the actual points
      //     ^ 0 for first dimension
    }
  
  // Clean up
  delete [] V;

  
  
  // ----- Compute the remaining dimensions -----
  for (unsigned i = 1; i < D; ++i)
    {
    
      // Read in parameters from file 
      unsigned d,
        // Size of the polynomial
        s,
        // Parameter a
        a;
      infile >> d >> s >> a;
      // Coefficients of the polynomial
      unsigned *m = new unsigned [s];
      for (unsigned k = 0; k < s; ++k)
        infile >> m[k];
      
      // Compute direction numbers V[1] to V[L], scaled by pow(2,32)
      unsigned *V = new unsigned [L];
      unsigned min = std::min(L, s);

      for (unsigned k = 0; k < min; ++k)
        V[k] = m[k] << (31 - k); 
      
      for (unsigned k = s; k < L; ++k)
        {
          V[k] = V[k - s] ^ (V[k - s] >> s); 
          for (unsigned l = 1; l < s; ++l) 
            V[k] ^= (((a >> (s - 1 - l)) & 1) * V[k - l]); 
        }
      
      unsigned x = 0;
      for (unsigned j = 0; j < N; ++j)
        {
          x ^= V[C[j]];
          POINTS[i][j] = (double)x / FACTOR; // *** the actual points
        }
  
      // Clean up
      delete [] m;
      delete [] V;
    }
  delete [] C;
  
  return POINTS;
}


int main(int argc, char **argv)
{
  if (argc != 4) {
    cout << endl << "input format: sobol N D FILENAME" << endl << endl;
    cout << "The program prints the first N sobol points in D dimensions." << endl;
    cout << "The points are generated in graycode order." << endl;
    cout << "The primitive polynomials and initial direction numbers are" << endl
	 << "given by the input file FILENAME." << endl << endl;
    return 0;
  }
  // Number of points
  int N = atoi(argv[1]);
  // Dimensions
  int D = atoi(argv[2]);
  double **P = sobol_points(N, D,argv[3]); 

  // display points
  cout << setprecision(20);
  //cout << setiosflags(ios::scientific) << setprecision(10);
  for (unsigned j = 0; j < N; ++j)
    {
      for (unsigned i = 0; i < D; ++i)
        cout << P[i][j] << " " ;
      cout << endl;
    }
  cout << endl;
}
