#ifndef M_PI
#define M_PI 3.14159265358979323846
#endif
#include <fstream>
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <pari/pari.h>
//#include <pari.h>
#include <time.h>
#include <string.h>
#define PARI_OLD_NAMES
#include <iostream>

using namespace std;

// Some functions for random sample generation
double Uniform(void) {
	return ((double)rand()+1.0)/((double)RAND_MAX+2.0);
} 
/*********************************
Standard Normal Distribution: use Box-Muller method
**********************************/
double Normal(void) {
	return sqrt( -log(Uniform())*2.0 ) * sin( 2.0*M_PI*Uniform() );
}
/*******************************
Gaussian Distribution
********************************/
double Gauss(double mu, double sigma) {   
	double z=sqrt( -2.0*log(Uniform()) ) * sin( 2.0*M_PI*Uniform() );
	return mu + sigma*z;
}
/********************************************************************
Error sampling function
GEN Sample(
	int n			: polynomial dimension
	double sigma	: standard deviation parameter 

Contents :  Create n dimension random number vector(signed integer) based on Gaussian distribution (0, σ)
********************************************************************/
GEN Sample(int n, double sigma)
{
	GEN ret	= cgetg(n + 1, t_VEC);
	double z;
	int i;
	
	for (i = 1; i <= n; i++) {
		z = Gauss(0, sigma); z = abs(round(z)); /*absolute value of Gaussian distribution */
		ret[i] = (long) stoi((long) z);
	}
	
	return ret;
}

GEN randomElement(int n){
	GEN ret;
	ret = cgetg(n + 1, t_VEC);
	for(int i=0; i<n; i++){
		//gel(ret, i+1) = stoi(rand());
		gel(ret, i+1) = lift(gmodulo(stoi(rand()), stoi(3)));
	}
	//pari_printf("ret: %s\n", GENtostr(ret));
	return ret;
}

GEN randomElementredbyt(int n, GEN t){
	GEN ret;
	ret = cgetg(n + 1, t_VEC);
	for(int i=0; i<n; i++){
		gel(ret, i+1) = lift(gmodulo(stoi(rand()), stoi(3)));
		//gel(ret, i+1) = stoi(3);
		//GEN tby2 = gfloor(gdiv(t, stoi(2)));
		//gel(ret, i+1) = gsub(gel(ret, i+1), tby2);
	}
	//pari_printf("ret: %s\n", GENtostr(ret));
	return ret;
}

void homomorphic(GEN n, GEN q, GEN t){
	GEN e, s, c, qbyt, m, h, finv, f, fdash, g, modulus, temp1, temp2, one, temp3, s1, e1, c1, m1;
	one = stoi(1);
	temp1 = cgetg(itos(n) + 2, t_VEC);
	for(int i=0; i<itos(n)+1; i++){
		gel(temp1, i+1) = stoi(0);
	}
	gel(temp1, 1) = stoi(1);
	gel(temp1, itos(n)+1) = stoi(1);
	modulus = gtopoly(temp1, -1);
	temp1 = cgetg(itos(n) + 1, t_VEC);
	temp2 = cgetg(itos(n) + 1, t_VEC);
	temp1 = randomElement(itos(n));
	temp2 = randomElement(itos(n));
	fdash = gtopolyrev(temp1,-1);
	g = gtopolyrev(temp2, -1);
	fdash = gmodulo(fdash, q);
	fdash = gmodulo(fdash, modulus);
	g = gmodulo(g, q);
	g = gmodulo(g, modulus);
	//pari_printf("f': %s\n", GENtostr(fdash));
	f = gmul(t, fdash);
	f = gadd(f, one);
	//pari_printf("f^2': %s\n", GENtostr(gmul(fdash, fdash)));
	//return;
	// finding the inverse of the element f in the polynomial ring.
	finv = ginvmod(f, modulus);
	pari_printf("Inverse Check: %s\n", GENtostr(gmul(finv, f)));
	h = gmul(t, g);
	h = gmul(h, finv);
	//pari_printf("Public Key: %s\n", GENtostr(h));
	//cout<<"Keys have been successfully created\n";
	//cout<<"Testing a relevant message for the sake of presentation\n";
	temp1 = cgetg(itos(n) + 1, t_VEC);
	temp3 = cgetg(itos(n) + 1, t_VEC);
	temp3 = randomElementredbyt(itos(n), t);
	//pari_printf("Message: %s\n\n\n\n\n\n\n\n\n\n\n\n", GENtostr(temp3));
	//return;
	//temp3 = temp1;
	m = gtopolyrev(temp3, -1);
	temp3 = cgetg(itos(n) + 1, t_VEC);
	temp3 = randomElementredbyt(itos(n), t);
	m1 = gtopolyrev(temp3, -1);
	m = gmodulo(m, q);
	m = gmodulo(m, modulus);

	m1 = gmodulo(m1, q);
	m1 = gmodulo(m1, modulus);
	//pari_printf("Message: %s\n\n\n\n\n\n\n\n\n\n\n\n", GENtostr(m));
	GEN two = stoi(2);
	//temp2 = gdiv(one, two);
	//pari_printf("Message: %s\n", GENtostr(floorr(temp2)));
	qbyt = gfloor(gdiv(q, t));
	//pari_printf("q/t: %s\n", GENtostr(qbyt));
	e = Sample(itos(n), 2);
	e = gtopolyrev(e, -1);
	s = Sample(itos(n), 2);
	s = gtopolyrev(s, -1);
	e1 = Sample(itos(n), 2);
	e1 = gtopolyrev(e1, -1);
	s1 = Sample(itos(n), 2);
	s1 = gtopolyrev(s1, -1);
	//pari_printf("s: %s\n", GENtostr(s));
	// check error dist whether gaussian allowed or not.
	e = gmodulo(e, q);
	e = gmodulo(e, modulus);
	s = gmodulo(s, q);
	s = gmodulo(s, modulus);
	e1 = gmodulo(e1, q);
	e1 = gmodulo(e1, modulus);
	s1 = gmodulo(s1, q);
	s1 = gmodulo(s1, modulus);
	// errors are ready now;
	temp1 = gmul(h, s);
	temp2 = gmul(h, s1);
	c = gadd(e, temp1);
	c1 = gadd(e, temp1);
	//cout<<GENtostr(gtovecrev(m))<<endl;
	GEN mold, m1old;
	mold = m;
	m1old = m1;
	
	//cout<<GENtostr(gtovecrev(lift(lift(temp1))))<<endl;
	//return;
	m = gtovecrev(lift(lift(m)));
	m1 = gtovecrev(lift(lift(m1)));
	//cout<<lg(m)-1<<" "<<lg(m1)-1;
	//return;
	cout<<"Before Comparison\n";
	//cout<<lg(m1)-1<<endl;
	for(int i=1; i<=itos(n); i++){
		//cout<<"a\n";
		//if(gcmp(gmul(two,gel(m, i)),q)==1){
		//	gel(m, i) = gsub(gel(m,i), q);
		//}
		gel(m, i) = gmul(qbyt, gel(m, i));
		//cout<<i<<endl;
		//if(gcmp(gmul(two,gel(m1, i)),q)==1){
		//	gel(m1, i) = gsub(gel(m1,i), q);
		//}
		gel(m1, i) = gmul(qbyt, gel(m1, i));
	}
	m = gtopolyrev(m, -1);
	m = gmodulo(m, q);
	m = gmodulo(m, modulus);
	m1 = gtopolyrev(m1, -1);
	m1 = gmodulo(m1, q);
	m1 = gmodulo(m1, modulus);
	c = gadd(c, m);
	c1 = gadd(c1, m1);
	c = gtovecrev(lift(lift(c)));
	c1 = gtovecrev(lift(lift(c1)));
	for(int i=1; i<=itos(n); i++){
		//cout<<"a\n";
		if(gcmp(gmul(two,gel(c, i)),q)==1){
			gel(c, i) = gsub(gel(c,i), q);
		}
		//gel(m, i) = gmul(qbyt, gel(m, i));
		//cout<<i<<endl;
		if(gcmp(gmul(two,gel(c1, i)),q)==1){
			gel(c1, i) = gsub(gel(c1,i), q);
		}
		//gel(m1, i) = gmul(qbyt, gel(m1, i));
	}
	c = gtopolyrev(c, -1);
	c = gmodulo(c, modulus);
	c1 = gtopolyrev(c1, -1);
	c1 = gmodulo(c1, modulus);
	//pari_printf("interm: %s\n", GENtostr(c));
	
	//temp1 = lift(lift(c));
	//temp1 = gtovecrev(temp1);
	//temp2 = lift(lift(c1));
	//temp2 = gtovecrev(temp2);
	//cout<<lg(temp1)-1<<endl;
	/*for(int i=0; i<itos(n); i++){
		//cout<<i<<endl;
		temp2 = gmul(gel(temp1, i+1), stoi(2));
		if(gcmp(temp2, q)>=0){
			gel(temp1, i+1) = gsub(gel(temp1, i+1), q);
		}
	}*/
	cout<<"here\n";
	GEN c2;
	c2 = gmul(c, c1);
	cout<<"mul done\n";
	temp1 = gtovecrev(lift(c2));
	for(int i=1; i<=itos(n); i++){
		//if(gcmp(gmul(two,gel(temp1, i)),q)==1){
		//	gel(temp1, i) = gsub(gel(temp1,i), q);
		//}
		//cout<<GENtostr(gel(temp1,i))<<"    ";
		gel(temp1, i) = diviiround(gmul(gel(temp1, i), t), q);
		//cout<<GENtostr(gel(temp1,i))<<endl;
	}
	c = gtopolyrev(temp1, -1);
	//c = gmodulo(c, q);
	c = gmodulo(c, modulus);
	cout<<"b\n";
	//cout<<GENtostr(c)<<endl;
	//pari_printf(": %d %d\n", (cmpii(one, two)), (cmpii(two, one)));
	// ciphertext computed
	//pari_printf("Ciphertext: %s\n", GENtostr(c));
	//cout<<GENtostr(f)<<endl;
	temp3 = f;
	f = gmul(f, temp3);
	/*temp3 = gtovecrev(lift(lift(f)));
	GEN temp4;
	temp4 = cgetg(itos(n) + 1, t_VEC);
	for(int i=0; i<itos(n); i++){
		gel(temp4, i+1) = lift(gmodulo(gmul(gel(temp3, i+1), gel(temp3, i+1)), q));
	}
	
	f = gtopolyrev(temp4, -1);
	f = gmodulo(f, q);
	f = gmodulo(f, modulus);*/
	//cout<<GENtostr(f)<<endl;
	cout<<"f-square\n";
	//f = gmul(f, f);
	f = lift(lift(f));
	f = gmodulo(f, modulus);
	temp1 = lift(gmul(f, c));
	temp1 = lift(gmodulo(temp1, q));
	temp1 = gtovecrev(temp1);
	for(int i=1; i<=itos(n); i++){
		if(gcmp(gmul(two,gel(temp1, i)),q)==1){
			gel(temp1, i) = gsub(gel(temp1,i), q);
		}
	}
	//cout<<GENtostr(temp1)<<endl;
	cout<<"vc\n";
	
	// maybe 0 to q-1 modular range required here.
	for(int i=1; i<=itos(n); i++){
		//if(gcmp(gmul(two,gel(temp1, i)),q)==1){
		//	gel(temp1, i) = gsub(gel(temp1,i), q);
			//cout<<GENtostr(gel(temp1,i))<<"    ";
		//}
		//cout<<GENtostr(gel(temp1,i))<<"    ";
		gel(temp1, i) = diviiround(gmul(gel(temp1, i), t), q);
		//cout<<GENtostr(gel(temp1,i))<<endl;
	}
	temp1 = lift(gmodulo(temp1, t));
	for(int i=1; i<=itos(n); i++){
		//cout<<"a\n";
		if(gcmp(gmul(two,gel(temp1, i)),t)==1){
			//gel(temp1, i) = gsub(gel(temp1,i), t);
		}
		
	}
	//cout<<GENtostr(temp1)<<endl;
	c = gtopolyrev(temp1, -1);
	//c = gmodulo(c, t);
	
	c = gmodulo(c, modulus);
	//cout<<GENtostr(c)<<endl;
	temp1 = lift(c);
	temp1 = gtovecrev(temp1);
	mold = gmodulo(gmodulo(lift(lift(mold)), modulus), t);
	m1old = gmodulo(gmodulo(lift(lift(m1old)), modulus), t);
	temp3 = gmul(mold, m1old);
	//cout<<GENtostr(lift(gmodulo(gtovecrev(lift(lift(m))), t)))<<endl;

	temp3 = gtovecrev(lift(lift(temp3)));

	temp3 = gtopolyrev(temp3, -1);
	temp3 = gmodulo(temp3, t);
	temp3 = gtovecrev(lift(temp3));
	for(int i=1; i<=itos(n); i++){
		//cout<<"a\n";
		if(gcmp(gmul(two,gel(temp3, i)),t)==1){
			//gel(temp3, i) = gsub(gel(temp3,i), t);
		}
		
	}
	//cout<<GENtostr(temp1);

	//cout<<GENtostr(gmul(lift(mold), lift(m1old)))<<endl;

	//pari_printf("\n%s\n", GENtostr(gfloor(qbyt)));
	//for(int i=0; i<itos(n); i++){
	//	//cout<<i<<endl;
	//	temp2 = gmul(gel(temp1, i+1), stoi(2));
	//	if(gcmp(temp2, t)>=0){
	//		gel(temp1, i+1) = gsub(gel(temp1, i+1), t);
	//	}
	//}
	cout<<"a\n";
	int correct=0, wrong = 0;
	for(int i=0; i<itos(n); i++){
		//cout<<"in1\n";
		if(gcmp(gel(temp1, i+1), gel(temp3, i+1))==0){
			correct++;
			cout<<"found "<<GENtostr(gel(temp1, i+1))<<"    "<<GENtostr(gel(temp3, i+1))<<endl;
		}
		else{
			cout<<"ERROR "<<GENtostr(gel(temp1, i+1))<<"    "<<GENtostr(gel(temp3, i+1))<<endl;
			wrong++;
			//cout<<"---------------------------------\n";	
		}
		//cout<<"1"<<endl;

	}
	cout<<correct<<"     "<<wrong<<endl;
	//pari_printf("Decrypted Ciphertext: %s\n", GENtostr(temp1));//, GENtostr(gtovecrev(lift(lift(m)))));
}

int main(){
	pari_init(2000000000,2);
	//GEN a;
	//a = gadd(stoi(45), stoi(1));
	//pari_printf("%s\n", GENtostr(a));
	//cout<<rand()<<" "<<rand()<<endl;
	GEN n, q, t;
	cout<<"Input n, q, and t in order\n";
	//n = gp_read_stream(stdin);
	//q = gp_read_stream(stdin);
	//t = gp_read_stream(stdin);
	n = stoi(2048);
	//q = stoi(1);
	//q = powii(stoi(2), stoi(383));
	//q = gsub(q, stoi(8589934592));
	//q = gadd(q, stoi(1));
	GEN temp;
	temp = powii(stoi(2), stoi(300));
	q = nextprime(temp);
	//t = stoi(10240000);
	t = stoi(10995120046099999);
	//t = gmul(t, stoi(1099512004609));
	pari_printf("%s %s %s\n", GENtostr(n), GENtostr(q), GENtostr(t));
	cout<<"calling the homomorphic encryption system\n";
	homomorphic(n, q, t);
	pari_close();
	return 0;
}