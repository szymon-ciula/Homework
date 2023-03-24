// Szymon Ciula
#include <iostream>

using namespace std;

class Punkt{
public:
  Punkt() : x(0), y(0) {}
  Punkt(double _x, double _y) : x(_x), y(_y) {}
  double x,y;
};

Punkt operator+ (const Punkt& a, const Punkt& b)
{   return Punkt(a.x+b.x,a.y+b.y);  }

Punkt operator- (const Punkt& a, const Punkt& b)
{   return Punkt(a.x-b.x,a.y-b.y);  }

bool operator== (const Punkt& a, const Punkt& b)
{   return (a.x==b.x ? (a.y==b.y ? true : false) : false);  }

bool operator!= (const Punkt& a, const Punkt& b)
{   return (a.x!=b.x ? (a.y!=b.y ? true : false) : false);  }

bool operator< (const Punkt& a, const Punkt& b)
{
    if(a.x<b.x)
        return true;
    else if(a.x > b.x)
        return false;
    else
    {
        if(a.y<b.y)
            return true;
        else
            return false;
    }
}

bool operator>=(const Punkt& a, const Punkt& b)
{   return !(a<b);  }

bool operator>(const Punkt& a, const Punkt& b)
{   return !(b>=a); }

bool operator<= (const Punkt& a, const Punkt& b)
{   return !(a>b);  }

ostream& operator<<(ostream& o, const Punkt& a)
{   return (o << '(' << a.x << ',' << a.y << ')');  }

class Wektor
{
    double x, y ,z;
public:
    Wektor(double x, double y, double z) : x{x}, y{y}, z{z} {}

    Wektor operator+ (const Wektor& b)
    {   return Wektor(x+b.x, y+b.y, z+b.z); }
    Wektor operator- (const Wektor& b)
    {   return Wektor(x-b.x, y-b.y, z-b.z); }
    Wektor operator* (const Wektor& b)
    {   return Wektor(x*b.x, y*b.y, z*b.z); }


    friend Wektor operator* (double a, const Wektor& w);
    friend Wektor operator* (const Wektor& w, double a);
    friend ostream& operator<< (ostream& o, const Wektor& a);
};

Wektor operator* (double a, const Wektor& w)
{   return Wektor(a*w.x, a*w.y, a*w.z); }
Wektor operator* (const Wektor& w, double a)
{   return Wektor(a*w.x, a*w.y, a*w.z); }
ostream& operator<<(ostream& o, const Wektor& a)
{   return (o << '(' << a.x << ',' << a.y << ',' << a.z << ')');    }

class Wielomian
{
private:
    double* wspolczynniki;
    unsigned int stopien;
public:
    Wielomian() : stopien{0}
    {
        wspolczynniki = new double[1];
        *wspolczynniki = 0;
    }
    Wielomian(unsigned int st, const double* wsp) : stopien{st}
    {
        wspolczynniki = new double[st+1];
        for(unsigned int i=0; i<=st; ++i)
            wspolczynniki[i] = *wsp++;
    }
    ~Wielomian()
    {   delete [] wspolczynniki;    }
    Wielomian(const Wielomian& b)
    {
        stopien = b.stopien;
        wspolczynniki = new double[b.stopien+1];
        for(unsigned int i=0; i<=stopien; ++i)
            wspolczynniki[i] = b.wspolczynniki[i];
    }
    Wielomian& operator= (const Wielomian& b)
    {
        if(this!=&b)
        {
            delete [] wspolczynniki;
            stopien = b.stopien;
            wspolczynniki = new double[b.stopien+1];
            for(unsigned int i=0; i<=stopien; ++i)
                wspolczynniki[i] = b.wspolczynniki[i];
        }
        return *this;
    }
    Wielomian operator+ (const Wielomian& b)
    {
        unsigned int st = (stopien>=b.stopien ? stopien : b.stopien);
        double tab[st];
        for(unsigned int i=0; i<=st; ++i)
            tab[i] = 0;
        for(unsigned int i=0; i<=stopien; ++i)
            tab[i] += wspolczynniki[i];
        for(unsigned int i=0; i<b.stopien; ++i)
            tab[i] += b.wspolczynniki[i];
    }
    Wielomian operator- (const Wielomian& b)
    {
        unsigned int st = (stopien>=b.stopien ? stopien : b.stopien);
        double tab[st];
        for(unsigned int i=0; i<=st; ++i)
            tab[i] = 0;
        for(unsigned int i=0; i<=stopien; ++i)
            tab[i] += wspolczynniki[i];
        for(unsigned int i=0; i<b.stopien; ++i)
            tab[i] -= b.wspolczynniki[i];
    }

    double& operator[] (unsigned int i)
    {   return wspolczynniki[i];    }
    long double operator()(double x)
    {
        long double wynik=0;
        for(unsigned int i=stopien; i>=0; --i)
            wynik = (wynik+wspolczynniki[i])*x;
        return wynik+wspolczynniki[0];
    }
};

int main()
{


    return 0;
}
