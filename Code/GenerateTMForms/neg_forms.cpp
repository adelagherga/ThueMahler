#include <iostream>
#include <cmath>
#include <algorithm>
#include <set>
using namespace std;


#include <gsl/gsl_poly.h>
///////

const int64_t ten = 10;
const int64_t ten2 = 100;
const int64_t ten3 = 1000;
const int64_t X=4*3*ten3*ten3+10;// add a little fudge just in case.



/////////////
int64_t a,b,c,d;
set<int64_t> products;

int64_t discrim(void) {
  return( -27*a*a*d*d+18*a*d*c*b + b*b*c*c-4*(b*b*b*d + c*c*c*a) );
}

bool check_nice(int64_t disc) {
  // need this to be 4*prime.
  // check divisible by 4
  if( (disc>0)||(disc< -X) ) return(0);

  disc *=-1;
  if( disc&3 ) return(0);

  return(1);
}

bool check_reduced(void) {
  if( d*a<=-(a-b)*(a-b+c) )return(0);
  if( d*a>=(a+b)*(a+b+c) ) return(0);

  if( (b==0)&&(d<=0) ) return(0);

//   if( d*d-a*a <= b*d-a*c ) return(0);
  if( d*(d-b) <= a*(a-c) ) return(0); // equiv to d*d-a*a<=b*d-a*c

  int64_t tmp=abs(__gcd( __gcd(a,b), __gcd(c,d) ));
  if( tmp==1  ||  tmp==3 ) return(1);
  else return(0);
}

int64_t cubes[23]={125, 343, 1331, 2197, 4913, 6859, 12167, 24389, 29791, 50653, 68921, 79507, 103823, 148877, 205379, 226981, 300763, 357911, 389017, 493039, 571787, 704969, 912673};

bool other_checks(int64_t disc) { // disc is always>0 here
  if( disc%8 == 0) return(0); // disc not multiple of 2^3=8
  if( disc%729 == 0) return(0); // disc not multiple of 3^6=729
  if( disc%27 == 0 ) {
    if( (b%3 != 0) || (c%3!=0) ) return(0); // when disc =27*blah, must have 3|b and 3|c.
  }
  for(int k=0; k<23; k++) {
    if(disc < k) return(1);
    if(disc % cubes[k] == 0) return(0);
  }
  if(disc > ten3*ten3) {
    if(disc%27!=0) return(0);
    if(disc%81==0) return(0);
  }
  return(1);
}

double sqr(const double &x) { return(x*x); }


int main(void) {

  double Xr = sqrt(X);

  double abound, bbound, cbound, dboundl, dboundu;
  int64_t disc;

  abound = pow( 16.0L*X/27.0L, 0.25L);
  for(a=1; a<=abound; a++) {

    bbound = a*1.5L + sqrt( Xr/sqrt(3.0L) - a*a*0.75L);
    for(b=0; b<=bbound; b++) {

      cbound = pow(X/(a*4.0L), 1.0L/3.0L);

      if(3*a>=2*b) cbound += b*b/(3.0L*a);
      else cbound += b- 0.75L*a;

      for(c=1-b; c<=cbound; c++) {

	dboundl = -((a-b)*(a-b+c))/(1.0L*a);
	dboundu = (a+b)*(a+b+c)/(1.0L*a);

	for(d=dboundl; d<=dboundu; d++) {
	  if( check_reduced() ) {
	    disc=discrim();
	    if( check_nice(disc) )  {
	      disc >>=2;
		if(other_checks(-disc)) cout << disc << " " << a << " " << b << " " << c << " " << d << endl;
	    }
	  }
	}
      }
    }
  }
}
