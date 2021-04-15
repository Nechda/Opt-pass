#include <stdio.h>
#include <stdlib.h>


int global = 0;

#define make_function(index)\
    void function_##index(){global = index;}

#define f(index)\
    function_##index()

make_function(0)
make_function(1)
make_function(2)


int main(int argc, char** argv)
{
    int N = atoi(argv[1]);
    N = (N >> 1) << 4 | N | 0x7ABE;
    switch (N % 10)
    {
        case 0:
            f(0);
        break;
        case 1:
            f(1);
        break;
        default:
            f(0);
        break;
    }

    f(2);

    if(N & 1)
    {
        f(0);
    }
    else
    {
        f(1);
        f(2);
    }
}
