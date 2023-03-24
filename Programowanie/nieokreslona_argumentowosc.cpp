//Szymon Ciula
#include <iostream>
#include <cstdarg>
#include <cmath>

using namespace std;

long double sum(const char* type, ...);
long double arithmetic_average(const char* type, ...);
long double geometric_average(const char* type, ...);
long double harmonic_average(const char* type, ...);

int main()
{
    cout << sum("iIdDfFiIdD", 1,2,3.,4.,5.,6.,7,8,9.,10.) << '\n'
         << arithmetic_average("iIdDfFiIdD", 1,2,3.,4.,5.,6.,7,8,9.,10.) << '\n'
         << geometric_average("iIdDfFiIdD", 1,2,3.,4.,5.,6.,7,8,9.,10.) << '\n'
         << harmonic_average("iIdDfFiIdD", 1,2,3.,4.,5.,6.,7,8,9.,10.) << endl;

    return 0;
}

long double sum(const char* type, ...)
{
    va_list ap;
    va_start(ap,type);
    long double result = 0;
    int i = 0;

    if(type)
    {
        char c;
        while ( (c = type[i++]) != '\0' )
        {
            switch (c)
            {
                case 'i':
                case 'I':
                    result += va_arg(ap,int);
                    break;
                case 'd':
                case 'D':
                case 'f':
                case 'F':
                    result += va_arg(ap,double);
                    break;
                default:
                    goto END;
            }
        }
    }
END:
    va_end(ap);
    return result;
}

long double arithmetic_average(const char* type, ...)
{
    va_list ap;
    va_start(ap,type);
    long double result = 0;
    int i = 0;

    if(type)
    {
        char c;
        while( (c = type[i++]) != '\0' )
        {
            switch(c)
            {
                case 'i':
                case 'I':
                    result += va_arg(ap,int);
                    break;
                case 'd':
                case 'D':
                case 'f':
                case 'F':
                    result += va_arg(ap,double);
                    break;
                default:
                    goto END;
            }
        }
    }
END:
    va_end(ap);
    return ((i!=1) ? result/(i-1) : 0);
}

long double geometric_average(const char* type, ...)
{
    va_list ap;
    va_start(ap,type);
    long double result = 1;
    int i = 0;

    if(type)
    {
        char c;
        while( (c = type[i++]) != '\0' )
        {
            switch(c)
            {
                case 'i':
                case 'I':
                    result *= va_arg(ap,int);
                    break;
                case 'd':
                case 'D':
                case 'f':
                case 'F':
                    result *= va_arg(ap,double);
                    break;
                default:
                    goto END;
            }
        }
    }
END:
    va_end(ap);
    return powl(result, 1.0/(i-1));
}

long double harmonic_average(const char* type, ...)
{
    va_list ap;
    va_start(ap,type);
    long double result = 0;
    int i = 0;

    if(type)
    {
        char c;
        while( (c=type[i++]) != '\0' )
        {
            switch(c)
            {
                case 'i':
                case 'I':
                    result += 1.0/va_arg(ap,int);
                    break;
                case 'd':
                case 'D':
                case 'f':
                case 'F':
                    result += 1.0/va_arg(ap,double);
                    break;
                default:
                    goto END;
            }
        }
    }
END:
    va_end(ap);
    return (long double)(i/result);
}

