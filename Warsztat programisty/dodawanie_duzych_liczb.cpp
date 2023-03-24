#include <iostream>

using namespace std;

void reverse_array(char* const liczba, const unsigned int dlugosc)
{
    char wynik[dlugosc];
    char *ptr_wynik = wynik;
    char *ptr_liczba = liczba+dlugosc-1;

    for(int i=dlugosc; i>0; --i)
        *ptr_wynik++ = *ptr_liczba--;

    ptr_liczba++;
    ptr_wynik = wynik;

    for(int i=dlugosc; i>0; --i)
        *ptr_liczba++ = *ptr_wynik++;
}

int main()
{
    char liczba1[256] = "98765432";
    char liczba2[256] = "12345678";
    unsigned int dlugosc1=0, dlugosc2=0;

//liczenie dlugosci
    char *ptr=liczba1;
    while(*ptr++ != 0)
        dlugosc1++;
    ptr=liczba2;
    while(*ptr++ != 0)
        dlugosc2++;

//odwracanie liczb
    reverse_array(liczba1, dlugosc1);
    reverse_array(liczba2, dlugosc2);

//zmienne pomocnicze
    unsigned int mniejsza_dlugosc;
    unsigned int wieksza_dlugosc;
    char *dluzsza;
//inicjalizacja w.w. zmiennych
    if(dlugosc1>dlugosc2)
    {
        mniejsza_dlugosc = dlugosc2;
        wieksza_dlugosc = dlugosc1;
        dluzsza = liczba1;
    }
    else
    {
        mniejsza_dlugosc = dlugosc1;
        wieksza_dlugosc = dlugosc2;
        dluzsza = liczba2;
    }

    char wynik[mniejsza_dlugosc+1];
    short przesuniecie = 0, suma;
//zmienne do iterowania
    char *ptr_wynik = wynik;
    char *ptr1 = liczba1, *ptr2 = liczba2;

//dodajemy cyfry az dobrniemy do konca krotszej liczby
    for(int i=mniejsza_dlugosc-1; i>=0; --i)
    {
        suma = przesuniecie+(*ptr1++)+(*ptr2++)-2*'0';
        if(suma>9)
        {
            przesuniecie = 1;
            *ptr_wynik++ = suma-10+'0';
        }
        else
        {
            przesuniecie = 0;
            *ptr_wynik++ = suma+'0';
        }
    }

//jesli dlugosci sa takie same, to wystarczy dodac na poczatku liczby przesuniecie
    if(dlugosc1==dlugosc2)
        *ptr_wynik = przesuniecie+'0';
    else
    {
        dluzsza += mniejsza_dlugosc;
    //Do nastepnej cyfry trzeba dodac przeniesienie.
    //Moze nastapic sytuacja, ze od tego miejsca dluzsza liczba ma pewna ilosc 9,
    //wiec zmieniamy wszystkie 9 na 0, az dojdziemy do poczatku liczby lub innej cyfry.
        if(przesuniecie == 1)
        {
            while(mniejsza_dlugosc<wieksza_dlugosc)
            {
                if(*ptr_wynik=='9')
                    *ptr_wynik++ = '0';
                else
                {
                    *ptr_wynik++ = przesuniecie+*dluzsza;
                    przesuniecie = 0;
                    break;
                }
                dluzsza++;
            }
        }

    //Przepisujemy reszte cyfr dluzszej liczby do naszej liczby wynikowej.
        for(unsigned int i=wieksza_dlugosc-mniejsza_dlugosc; i>0; --i)
            *ptr_wynik++ = *dluzsza++;
    //Gdyby petla while skonczyla sie z powodu dotarcia do konca liczby, przesuniecie wynosiloby 1.
    //Trzeba pamietac o dodaniu go na poczatku liczby.
        *ptr_wynik = przesuniecie+'0';
    }

//Wypisujemy liczbe pomijajac ewentualne 0 poczatkowe.
    if(*ptr_wynik=='0')
        ptr_wynik--;
    do
        cout << *ptr_wynik--;
    while(ptr_wynik >= wynik);

    return 0;
}
