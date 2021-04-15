#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>
#include <math.h>
#include <time.h>

float getRandom()
{
    const unsigned L = 10000;
    return ( rand() % L ) / (float)L;
}

bool isZero(float number)
{
    const float accuracy = 1e-4;
    return fabs(number) < accuracy;
}

//solve ax+b = 0
int solveLinear(float a, float b)
{
    if(isZero(a))
    {
        if(isZero(b))
            return -1; //infty solutions
        else
            return 0; // doesn't exist solutions
    }
    else
        return 1; // x = -b/a
}

//solve ax^2+bx+c = 0
int solveSquare(float a, float b, float c)
{
    if(fabs(a) < 10e-7)
        return solveLinear(b,c);

    if(isZero(c))
        return 1 + solveLinear(a,b);

    float D = b*b - 4*a*c;
    if(isZero(D))
        return 1;
    if(D > 0)
        return 2;
    else
        return 0;

}

int main(int argc, char** argv)
{
    float a = 0;
    float b = 0;
    float c = 0;
    if(argc>1)
    {
        a = 3;
        b = 4;
        c = 5;
    }
    int nSolutions = solveSquare(a,b,c);
    printf("Equation %05f x^2 + %05f x + %05f = 0\n Has %d solutions. (-1 means infty)\n", a,b,c, nSolutions);
    return 0;
}
