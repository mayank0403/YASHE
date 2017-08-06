
/***************************************************************************
 
 YASHE by Bos et al. basic version (No relinearization supported in this version)
 implemented by Mayank (Roll No. - 14075033) and Babloo Kumar (Roll no. - 14074005)
 of CSE Part - III of IIT BHU as a part of the bigger CryptoML project undertaken as BTP
 (B.Tech Project) under the supervision of Prof. K.K.Shukla (HoD, CSE, IIT BHU).
 
 Dated: 21/04/2017.
 
 ***************************************************************************/

#ifndef M_PI
#define M_PI 3.14159265358979323846
#endif
#include <fstream>
#include <stdio.h>
#include <stdlib.h>
#include <cmath>
#include <pari/pari.h>
#include <time.h>
#include <string.h>
#define PARI_OLD_NAMES
#include <iostream>

using namespace std;

int verbose = 0;
int detailedverbose = 0;
int errorhalt = 0;

// Some functions for random sample generation
double Uniform(void) {
    return ((double)rand()+1.0)/((double)RAND_MAX+2.0);
}
/*********************************
 Standard Normal Distribution: using Box-Miller method
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
        gel(ret, i+1) = lift(gmodulo(stoi(rand()), stoi(300000)));
    }
    return ret;
}

GEN randomElementredbyt(int n, GEN t){
    GEN ret;
    ret = cgetg(n + 1, t_VEC);
    for(int i=0; i<n; i++){
        gel(ret, i+1) = lift(gmodulo(stoi(rand()), t));
    }
    return ret;
}

// Coefficient encoding of a single number into a polynomial
GEN encodeinput(GEN n, GEN t, long long int input){
    if(input>itos(t)){
        cout<<"[Error] Using the current encoding and t value, this input will give incorrect result due to reduction.";
        errorhalt = 1;
        return stoi(0);
    }
    GEN ret;
    ret = cgetg(itos(n) + 1, t_VEC);
    for(int i=0; i<itos(n); i++){
        if(i==0)
            gel(ret, i+1) = stoi(input);
        else
            gel(ret, i+1) = stoi(0);
    }
    if(verbose)
        cout<<"Input has been encoded\n";
    return ret;
}

// Coefficient encoding of an integer vector into a polynomial
GEN encodeinputvector(GEN n, GEN t, GEN input){
    GEN ret;
    ret = cgetg(itos(n) + 1, t_VEC);
    int len = lg(input)-1;
    for(int i=0; i<itos(n); i++){
        if(i<len)
            gel(ret, i+1) = gel(input, i+1);
        else
            gel(ret, i+1) = stoi(0);
    }
    return ret;
}

struct keyset{
    GEN pk;
    GEN sk;
    GEN finv = stoi(0);
};

struct params{
    GEN n;
    GEN q;
    GEN t;
    GEN modulus = stoi(0);
};

// Function to generate keys.
keyset* keygen(params* param){
    GEN n = param->n;
    GEN q = param->q;
    GEN t = param->t;
    keyset* keys = new keyset;
    GEN one = stoi(1);
    GEN temp, temp1, modulus, f, fdash, finv, g, h;
    temp = cgetg(itos(n) + 2, t_VEC);
    for(int i=0; i<itos(n)+1; i++){
        gel(temp, i+1) = stoi(0);
    }
    gel(temp, 1) = stoi(1);
    gel(temp, itos(n)+1) = stoi(1);
    modulus = gtopoly(temp, -1);
    param->modulus = modulus;
    
    do{
        temp1 = cgetg(itos(n) + 1, t_VEC);
        temp = cgetg(itos(n) + 1, t_VEC);
        temp1 = randomElement(itos(n));
        temp = randomElement(itos(n));
        fdash = gtopolyrev(temp1,-1);
        g = gtopolyrev(temp, -1);
        fdash = gmodulo(fdash, q);
        fdash = gmodulo(fdash, modulus);
        g = gmodulo(g, q);
        g = gmodulo(g, modulus);
        f = gmul(t, fdash);
        f = gadd(f, one);
        finv = ginvmod(f, modulus);
    }
    while (lg(finv)-1 != itos(n)); // Loop until an invertible f is found.
    
    h = gmul(t, g);
    h = gmul(h, finv);
    
    keys->pk = h;
    keys->sk = f;
    keys->finv = finv;
    return keys;
    
}

// Function to encrypt an integer vector in form of an element of the Ring R_q^n
GEN encrypt(GEN input, params* param, keyset* key){
    if(lg(input)-1 >= itos(param->n)){
        cout<<"The input vector cannot be greater than n"<<endl;
        return stoi(0);
    }
    GEN n = param->n;
    GEN q = param->q;
    GEN t = param->t;
    GEN modulus = param->modulus;
    GEN h = key->pk;
    
    GEN two = stoi(2);
    GEN temp, m, s, e, c, qbyt;
    
    qbyt = gfloor(gdiv(q, t));
    temp = cgetg(itos(n) + 1, t_VEC);
    temp = encodeinputvector(n, t, input);
    m = gtopolyrev(temp, -1);
    m = gmodulo(m, q);
    m = gmodulo(m, modulus);
    
    e = Sample(itos(n), 2);
    e = gtopolyrev(e, -1);
    s = Sample(itos(n), 2);
    s = gtopolyrev(s, -1);
    e = gmodulo(e, q);
    e = gmodulo(e, modulus);
    s = gmodulo(s, q);
    s = gmodulo(s, modulus);
    
    temp = gmul(h, s);
    c = gadd(e, temp);
    
    m = gtovecrev(lift(lift(m)));
    for(int i=1; i<=lg(m)-1; i++){
        gel(m, i) = gmul(qbyt, gel(m, i));
    }
    m = gtopolyrev(m, -1);
    m = gmodulo(m, q);
    m = gmodulo(m, modulus);
    c = gadd(c, m);
    
    // Mapping the ciphertext to the symmetric interval of (-q/2, q/2]
    
    c = gtovecrev(lift(lift(c)));
    for(int i=1; i<=itos(n); i++){
        if(gcmp(gmul(two,gel(c, i)),q)==1){
            gel(c, i) = gsub(gel(c,i), q);
        }
    }
    c = gtopolyrev(c, -1);
    c = gmodulo(c, modulus);
    
    return c;
    
}

// This decrypt function should be called when ciphertext is added homomorphically or it is a simple ciphertext
GEN decryptSimple(GEN input, params* param, keyset* key){
    
    GEN n = param->n;
    GEN q = param->q;
    GEN t = param->t;
    GEN modulus = param->modulus;
    GEN h = key->pk;
    GEN f = key->sk;
    GEN two = stoi(2);
    
    GEN temp, temp1;
    
    temp = lift(lift(gmul(f, input)));
    temp = gtovecrev(temp);
    for(int i=1; i<=itos(n); i++){
        while(gcmp(gmul(two,gel(temp, i)),q)==1){
            gel(temp, i) = gsub(gel(temp, i), q);
        }
    }
    
    for(int i=1; i<=itos(n); i++){
        gel(temp, i) = diviiround(gmul(gel(temp, i), t), q);
    }
    temp = lift(gmodulo(temp, t));
    temp1 = gtopolyrev(temp, -1);
    temp1 = gmodulo(temp1, modulus);
    temp = lift(temp1);
    temp = gtovecrev(temp);
    GEN result = stoi(0);
    for(int i=0; i<lg(temp)-1; i++){
        result = gadd(gel(temp, i+1), result);
    }
    
    cout<<"Simple decryption result "<<GENtostr(result)<<endl;
    
    return temp;
    
}

// This function should be used when the ciphertext has been operated using homomorphic multiplication.
GEN decryptOneMul(GEN input, params* param, keyset* key){
    
    GEN n = param->n;
    GEN q = param->q;
    GEN t = param->t;
    GEN modulus = param->modulus;
    GEN h = key->pk;
    GEN f = key->sk;
    GEN two = stoi(2);
    
    GEN temp, temp1, temp2;
    
    temp2 = f;
    temp2 = gmul(f, temp2);
    temp2 = lift(lift(temp2));
    temp2 = gmodulo(temp2, modulus);
    temp = lift(gmul(temp2, input));
    temp = lift(gmodulo(temp, q));
    temp = gtovecrev(temp);
    
    for(int i=1; i<=itos(n); i++){
        while(gcmp(gmul(two,gel(temp, i)),q)==1){
            gel(temp, i) = gsub(gel(temp, i), q);
        }
    }
    
    for(int i=1; i<=itos(n); i++){
        gel(temp, i) = diviiround(gmul(gel(temp, i), t), q);
    }
    temp = lift(gmodulo(temp, t));
    temp1 = gtopolyrev(temp, -1);
    temp1 = gmodulo(temp1, modulus);
    temp = lift(temp1);
    temp = gtovecrev(temp);
    GEN result = stoi(0);
    for(int i=0; i<lg(temp)-1; i++){
        result = gadd(gel(temp, i+1), result);
    }
    
    cout<<"Decryption result "<<GENtostr(result)<<endl;
    
    return temp;
    
}

// This function is used to homomorphically add 2 ciphertexts.
GEN homAdd(GEN input1, GEN input2){
    return gadd(input1, input2);
}

// This function is used to homomorphically multiply 2 ciphertexts. Currently, this function can only support one depth multiplications.
GEN homMul(GEN input1, GEN input2){
    return gmul(input1, input2);
}



// Function for performing homomorphic multiplication encoding the inputs as constant polynomials.

void homomorphicMul(GEN n, GEN q, GEN t, long long int input1, long long int input2){
    GEN e, s, c, qbyt, m, h, finv, f, fdash, g, modulus, temp1, temp2, one, temp3, s1, e1, c1, m1;
    one = stoi(1);
    // Creating the modulus polynomial f(x)
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
    f = gmul(t, fdash);
    f = gadd(f, one);
    // Finding the inverse of the element f in the polynomial ring.
    finv = ginvmod(f, modulus);
    h = gmul(t, g);
    h = gmul(h, finv);
    if(detailedverbose)
        pari_printf("Public Key: %s\n", GENtostr(h));
    cout<<"Keys have been successfully created.\n";
    cout<<"Encoding the inputs in form of constant polynomials for plaintext.\n";
    temp1 = cgetg(itos(n) + 1, t_VEC);
    temp3 = cgetg(itos(n) + 1, t_VEC);
    temp3 = encodeinput(n, t, input1);
    if(errorhalt)
        return;
    if(detailedverbose)
        pari_printf("Message1: \n\n\n%s\n\n\n", GENtostr(temp3));
    m = gtopolyrev(temp3, -1);
    temp3 = cgetg(itos(n) + 1, t_VEC);
    temp3 = encodeinput(n, t, input2);
    if(errorhalt)
        return;
    //if(detailedverbose)
    //pari_printf("Message2: %s\n\n\n\n\n\n", GENtostr(temp3));
    m1 = gtopolyrev(temp3, -1);
    
    m = gmodulo(m, q);
    m = gmodulo(m, modulus);
    m1 = gmodulo(m1, q);
    m1 = gmodulo(m1, modulus);
    cout<<"Finding error ring elements.\n";
    GEN two = stoi(2);
    qbyt = gfloor(gdiv(q, t));
    e = Sample(itos(n), 2);
    e = gtopolyrev(e, -1);
    s = Sample(itos(n), 2);
    s = gtopolyrev(s, -1);
    e1 = Sample(itos(n), 2);
    e1 = gtopolyrev(e1, -1);
    s1 = Sample(itos(n), 2);
    s1 = gtopolyrev(s1, -1);
    e = gmodulo(e, q);
    e = gmodulo(e, modulus);
    s = gmodulo(s, q);
    s = gmodulo(s, modulus);
    e1 = gmodulo(e1, q);
    e1 = gmodulo(e1, modulus);
    s1 = gmodulo(s1, q);
    s1 = gmodulo(s1, modulus);
    // errors are ready now;
    cout<<"All ring elements required have been generated.\n";
    temp1 = gmul(h, s);
    temp2 = gmul(h, s1);
    c = gadd(e, temp1);
    c1 = gadd(e, temp1);
    GEN mold, m1old;
    mold = m;
    m1old = m1;
    
    m = gtovecrev(lift(lift(m)));
    m1 = gtovecrev(lift(lift(m1)));
    for(int i=1; i<=lg(m)-1; i++){
        
        gel(m, i) = gmul(qbyt, gel(m, i));
        
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
    cout<<"Ciphertexts have been generated.\n";
    
    c = gtovecrev(lift(lift(c)));
    c1 = gtovecrev(lift(lift(c1)));
    for(int i=1; i<=itos(n); i++){
        if(gcmp(gmul(two,gel(c, i)),q)==1){
            gel(c, i) = gsub(gel(c,i), q);
        }
        if(gcmp(gmul(two,gel(c1, i)),q)==1){
            gel(c1, i) = gsub(gel(c1,i), q);
        }
    }
    if(detailedverbose)
        cout<<"Ciphertext1: "<<GENtostr(c)<<endl;
    c = gtopolyrev(c, -1);
    
    c = gmodulo(c, modulus);
    c1 = gtopolyrev(c1, -1);
    
    c1 = gmodulo(c1, modulus);
    cout<<"Ciphertexts coefficients mapped around q symmeterically.\n";
    
    GEN c2;
    c2 = gmul(c, c1);
    
    cout<<"Homomorphic multiplication done.\n";
    temp1 = gtovecrev(lift(c2));
    for(int i=1; i<=itos(n); i++){
        gel(temp1, i) = diviiround(gmul(gel(temp1, i), t), q);
        //cout<<GENtostr(gel(temp1,i))<<endl;
    }
    if(detailedverbose)
        cout<<"Ciphertext obtained by multipication: "<<GENtostr(temp1)<<endl;
    c = gtopolyrev(temp1, -1);
    
    c = gmodulo(c, modulus);
    
    temp3 = f;
    cout<<"Proceeding to decryption without relinearization by using f^2 ring element.\n";
    f = gmul(f, temp3);
    f = lift(lift(f));
    f = gmodulo(f, modulus);
    temp1 = lift(gmul(f, c));
    temp1 = lift(gmodulo(temp1, q));
    temp1 = gtovecrev(temp1);
    for(int i=1; i<=itos(n); i++){
        while(gcmp(gmul(two,gel(temp1, i)),q)==1){
            gel(temp1, i) = gsub(gel(temp1,i), q);
        }
    }
    
    // maybe 0 to q-1 modular range required here.
    for(int i=1; i<=itos(n); i++){
        gel(temp1, i) = diviiround(gmul(gel(temp1, i), t), q);
    }
    temp1 = lift(gmodulo(temp1, t));
    for(int i=1; i<=itos(n); i++){
        if(gcmp(gmul(two,gel(temp1, i)),t)==1){
        }
        
    }
    c = gtopolyrev(temp1, -1);
    
    c = gmodulo(c, modulus);
    //cout<<GENtostr(c)<<endl;
    temp1 = lift(c);
    temp1 = gtovecrev(temp1);
    cout<<"Decryption done, evaluating the results.\n";
    mold = gmodulo(gmodulo(lift(lift(mold)), modulus), t);
    m1old = gmodulo(gmodulo(lift(lift(m1old)), modulus), t);
    temp3 = gmul(mold, m1old);
    
    temp3 = gtovecrev(lift(lift(temp3)));
    
    temp3 = gtopolyrev(temp3, -1);
    temp3 = gmodulo(temp3, t);
    temp3 = gtovecrev(lift(temp3));
    int correct=0, wrong = 0;
    long long int result=0;
    for(int i=0; i<lg(temp1)-1; i++){
        result += itos(gel(temp1, i+1));
        
        if(gcmp(gel(temp1, i+1), gel(temp3, i+1))==0){
            correct++;
            //cout<<"found "<<GENtostr(gel(temp1, i+1))<<"    "<<GENtostr(gel(temp3, i+1))<<endl;
        }
        else{
            //cout<<"ERROR "<<GENtostr(gel(temp1, i+1))<<"    "<<GENtostr(gel(temp3, i+1))<<endl;
            wrong++;
        }
        
    }
    if(correct == lg(temp1)-1){
        cout<<"Operation successfully completed.\n";
    }
    else{
        cout<<"Error in computation.\n";
    }
    cout<<"--------------------------------------------------------------------------\n\nResult of computation is: "<<result<<"\n\n--------------------------------------------------------------------------"<<endl;
    
}

// Function for performing homomorphic addition encoding the inputs as constant polynomials.

void homomorphicAdd(GEN n, GEN q, GEN t, long long int input1, long long int input2){
    GEN e, s, c, qbyt, m, h, finv, f, fdash, g, modulus, temp1, temp2, one, temp3, s1, e1, c1, m1;
    one = stoi(1);
    // Creating the modulus polynomial f(x)
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
    f = gmul(t, fdash);
    f = gadd(f, one);
    // Finding the inverse of the element f in the polynomial ring.
    finv = ginvmod(f, modulus);
    h = gmul(t, g);
    h = gmul(h, finv);
    if(detailedverbose)
        pari_printf("Public Key: %s\n", GENtostr(h));
    cout<<"Keys have been successfully created.\n";
    cout<<"Encoding the inputs in form of constant polynomials for plaintext.\n";
    temp1 = cgetg(itos(n) + 1, t_VEC);
    temp3 = cgetg(itos(n) + 1, t_VEC);
    temp3 = encodeinput(n, t, input1);
    if(errorhalt)
        return;
    if(detailedverbose)
        pari_printf("Message1: \n\n\n%s\n\n\n", GENtostr(temp3));
    m = gtopolyrev(temp3, -1);
    temp3 = cgetg(itos(n) + 1, t_VEC);
    temp3 = encodeinput(n, t, input2);
    if(errorhalt)
        return;
    //if(detailedverbose)
    //	pari_printf("Message2: %s\n\n\n\n\n\n", GENtostr(temp3));
    m1 = gtopolyrev(temp3, -1);
    
    // Converting constant polynomials to Ring elements.
    
    m = gmodulo(m, q);
    m = gmodulo(m, modulus);
    m1 = gmodulo(m1, q);
    m1 = gmodulo(m1, modulus);
    cout<<"Finding error ring elements.\n";
    GEN two = stoi(2);
    qbyt = gfloor(gdiv(q, t));
    e = Sample(itos(n), 2);
    e = gtopolyrev(e, -1);
    s = Sample(itos(n), 2);
    s = gtopolyrev(s, -1);
    e1 = Sample(itos(n), 2);
    e1 = gtopolyrev(e1, -1);
    s1 = Sample(itos(n), 2);
    s1 = gtopolyrev(s1, -1);
    e = gmodulo(e, q);
    e = gmodulo(e, modulus);
    s = gmodulo(s, q);
    s = gmodulo(s, modulus);
    e1 = gmodulo(e1, q);
    e1 = gmodulo(e1, modulus);
    s1 = gmodulo(s1, q);
    s1 = gmodulo(s1, modulus);
    
    cout<<"All ring elements required have been generated.\n";
    // errors are ready now;
    temp1 = gmul(h, s);
    temp2 = gmul(h, s1);
    c = gadd(e, temp1);
    c1 = gadd(e, temp1);
    GEN mold, m1old;
    mold = m;
    m1old = m1;
    
    m = gtovecrev(lift(lift(m)));
    m1 = gtovecrev(lift(lift(m1)));
    for(int i=1; i<=lg(m)-1; i++){
        
        gel(m, i) = gmul(qbyt, gel(m, i));
        
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
    
    cout<<"Ciphertexts have been generated.\n";
    c = gtovecrev(lift(lift(c)));
    c1 = gtovecrev(lift(lift(c1)));
    for(int i=1; i<=itos(n); i++){
        if(gcmp(gmul(two,gel(c, i)),q)==1){
            gel(c, i) = gsub(gel(c,i), q);
        }
        if(gcmp(gmul(two,gel(c1, i)),q)==1){
            gel(c1, i) = gsub(gel(c1,i), q);
        }
    }
    if(detailedverbose)
        cout<<"Ciphertext1: "<<GENtostr(c)<<endl;
    c = gtopolyrev(c, -1);
    
    c = gmodulo(c, modulus);
    c1 = gtopolyrev(c1, -1);
    
    c1 = gmodulo(c1, modulus);
    
    cout<<"Ciphertexts coefficients mapped around q symmeterically.\n";
    GEN c2;
    c = gadd(c, c1);
    cout<<"Homomorphic addition done.\n";
    temp1 = lift(lift(gmul(f, c)));
    temp1 = gtovecrev(temp1);
    for(int i=1; i<=itos(n); i++){
        while(gcmp(gmul(two,gel(temp1, i)),q)==1){
            gel(temp1, i) = gsub(gel(temp1,i), q);
        }
    }
    if(detailedverbose)
        cout<<"Ciphertext obtained by addition: "<<GENtostr(c)<<endl;
    // maybe 0 to q-1 modular range required here.
    for(int i=1; i<=itos(n); i++){
        gel(temp1, i) = diviiround(gmul(gel(temp1, i), t), q);
    }
    temp1 = lift(gmodulo(temp1, t));
    c = gtopolyrev(temp1, -1);
    
    c = gmodulo(c, modulus);
    temp1 = lift(c);
    temp1 = gtovecrev(temp1);
    
    cout<<"Decryption done, evaluating the results.\n";
    mold = gmodulo(gmodulo(lift(lift(mold)), modulus), t);
    m1old = gmodulo(gmodulo(lift(lift(m1old)), modulus), t);
    temp3 = gadd(mold, m1old);
    
    temp3 = gtovecrev(lift(lift(temp3)));
    
    temp3 = gtopolyrev(temp3, -1);
    temp3 = gmodulo(temp3, t);
    temp3 = gtovecrev(lift(temp3));
    
    int correct=0, wrong = 0;
    long long int result = 0;
    for(int i=0; i<lg(temp1)-1; i++){
        
        result += itos(gel(temp1, i+1));
        if(gcmp(gel(temp1, i+1), gel(temp3, i+1))==0){
            correct++;
            //cout<<"found "<<GENtostr(gel(temp1, i+1))<<"    "<<GENtostr(gel(temp3, i+1))<<endl;
        }
        else{
            //cout<<"ERROR "<<GENtostr(gel(temp1, i+1))<<"    "<<GENtostr(gel(temp3, i+1))<<endl;
            wrong++;
            
        }
    }
    
    cout<<"--------------------------------------------------------------------------\n\nResult of computation is: "<<result<<"\n\n--------------------------------------------------------------------------"<<endl;
    
}

int main(){
    pari_init(2000000000,2);
    GEN n, q, t;
    cout<<"Parameters n, q, and t are already initialized.\n";
    n = stoi(8192);
    GEN temp;
    temp = powii(stoi(2), stoi(180));
    q = nextprime(temp);
    t = stoi(1000000);
    pari_printf("(n, q, t) = (%s, %s, %s)\n", GENtostr(n), GENtostr(q), GENtostr(t));
    cout<<"Enter the input integers:\n";
    long long int input1, input2;
    cin>>input1>>input2;
    cout<<"Enter the operation to perform (--|1 for Addition and 2 for Multiplication|--)\n";
    int flag;
    cin>>flag;
    cout<<"Enter the verbose mode (1 for verbose, 2 for detailed verbose and 0 for clean mode)"<<endl;
    cin>>verbose;
    if(verbose==2)
        detailedverbose = 1;
    if(flag-1){
        homomorphicMul(n, q, t, input1, input2);
    }
    else{
        homomorphicAdd(n, q, t, input1, input2);
    }
    cout<<"Cleaning up the Pari stack. Ending program.";
    pari_close();
    return 0;
}
