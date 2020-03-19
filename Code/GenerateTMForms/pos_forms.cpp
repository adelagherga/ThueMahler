#include <iostream>
#include <cmath>
#include <algorithm>
#include <map>
#include <list>

using namespace std;

#include <gsl/gsl_poly.h>
///////

const int64_t ten = 10;
const int64_t ten2 = 100;
const int64_t ten3 = 1000;
const int64_t X=4*3*ten3*ten3+10;// add a little fudge just in case.



/////////////
int64_t a,b,c,d;

map<int64_t, list<string> > forms;

int64_t discrim(void) {
  return( -27*a*a*d*d+18*a*d*c*b + b*b*c*c-4*(b*b*b*d + c*c*c*a) );
}

bool check_nice(int64_t disc) {
  // need this to be 4*prime.
  // check divisible by 4
  if( (disc<0)||(disc>X) ) return(0);

  if( disc & 3 ) return(0);
  else disc>>=2;

  return( 1 );
}

int64_t P,Q,R;
bool check_reduced(void) {
  if( (b==0)&&(d>=0) ) return(0);

  P=b*b-3*a*c;
  Q=b*c-9*a*d;
  R=c*c-3*b*d;

  if(abs(Q)>P) return(0);

  if(P>R) return(0);

  if( (Q==0)&&(d>=0) ) return(0);

  if( (P==Q)&&(b>=abs(3*a-b)) ) return(0);

  if(P==R) {
    if(a>abs(d)) return(0);
    if(a==abs(d) && (b>=abs(c))) return(0);
  }

  int64_t tmp=abs(__gcd( __gcd(a,b), __gcd(c,d) ));
  if( tmp==1  ||  tmp==3 ) return(1);
  else return(0);
}

int64_t cubes[23]={125, 343, 1331, 2197, 4913, 6859, 12167, 24389, 29791, 50653, 68921, 79507, 103823, 148877, 205379, 226981, 300763, 357911, 389017, 493039, 571787, 704969, 912673};

bool other_checks(int64_t disc) {
  if( disc%8 == 0) return(0); // disc not multiple of 2^3=8
  if( disc%729 == 0) return(0); // disc not multiple of 3^6=729
  if( disc%27 == 0 ) {
    if( (b%3 != 0) || (c%3!=0) ) return(0); // when disc =27*blah, must have 3|b and 3|c.
  }
  for(int k=0; k<23; k++) {
    if(disc<k) return(1);
    if(disc % cubes[k] == 0) return(0);
  }
  if(disc>ten3*ten3) {
    if(disc%27 !=0) return(0);
    if(disc%81 ==0) return(0);
  }
  return(1);
}


double sqr(const double &x) { return(x*x); }


int main(void) {

  double Xr = sqrt(X);

  double x0,x1,x2;

  double abound, bbound, cbound, dboundl, dboundu;
  int64_t disc;

  abound = sqrt( 4.0L*Xr/27.0L );
  for(a=1; a<=abound; a++) {

    bbound = a*1.5L + sqrt( Xr - (a*a*27.0L)/4.0L);
    for(b=0; b<=bbound; b++) {

      // format is to solve 1x^3 + A*x^2+B*X+C and store in x0,x1,x2. with x0<x1<x2
      if( gsl_poly_solve_cubic( -sqr(3.0L*a+2.0L*b)/4.0L, 0.0L, -(27.0L*a*a*X/4.0L),&x0,&x1,&x2) == 1) {
	// only 1 root and is stored in x0
	cbound = (b*b-abs(x0))/(3.0L*a);
      }
      else {
	// x2 should be biggest root.
	cbound = (b*b-abs(x2))/(3.0L*a);
      }

      for(c=ceil(cbound); c<=b-3*a; c++) { //c can be negative so check mod.

	dboundl = ( (b+3.0L*a)*c-b*b )/(a*9.0L);
	dboundu = ( (b-3.0L*a)*c+b*b )/(a*9.0L);

	for(d=dboundl; d<=dboundu; d++) {
	  if( check_reduced() ) {
	    disc=discrim();
	    if( check_nice(disc) )  { //d can be negative so check mod.
	        disc >>=2;
		if(other_checks(disc)) cout << disc << " " << a << " " << b << " " << c << " " << d << endl;
	    }
	  }
	}
      }
    }
  }


}
