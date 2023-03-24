//Szymon Ciula
#include <iostream>

using namespace std;

void remove_row(int** const ptr_arr, int* const ptr_dim, int& arr_size, const int& row_index);
void print(const int** ptr_arr, const int* ptr_dim, const int& arr_size);

int main()
{
    int liczba_wierszy;
    int *t_liczba_elementow;
    int **tablica;

//wprowadzanie zmiennych i tworzenie tablicy
    cin >> liczba_wierszy;

    t_liczba_elementow = static_cast<int*>( malloc(liczba_wierszy*sizeof(int)) );
    tablica = static_cast<int**>( malloc(liczba_wierszy*sizeof(int*)) );
    for(int i=0; i<liczba_wierszy; ++i)
    {
        cin >> t_liczba_elementow[i];

        tablica[i] = static_cast<int*>( malloc(t_liczba_elementow[i]*sizeof(int)) );
        for(int j=0; j<t_liczba_elementow[i]; ++j)
            tablica[i][j] = 10*i+j;
    }
//wypisywanie tablicy
    print(const_cast<const int**>(tablica), t_liczba_elementow, liczba_wierszy);
//wprowadzanie wspolrzednych prostokata
    int minc, minr, maxc, maxr;
    cin >> minr >> minc >> maxr >> maxc;

    if(maxr >= liczba_wierszy)  maxr = liczba_wierszy-1;
//usuwanie elementów z tablicy
    for(int i=minr; i<=maxr; )
    {
        if(maxc >= t_liczba_elementow[i])
            t_liczba_elementow[i] = minc;
        else
        {
            int roznica = maxc-minc+1;
            for(int j=minc; j<t_liczba_elementow[i]-roznica; ++j)
                tablica[i][j] = tablica[i][j+roznica];
            t_liczba_elementow[i] -= roznica;
        }

        if(t_liczba_elementow[i] == 0)
        {
            remove_row(tablica, t_liczba_elementow, liczba_wierszy, i);
            t_liczba_elementow = static_cast<int*>( realloc(t_liczba_elementow, liczba_wierszy*sizeof(int)) );
            tablica = static_cast<int**>( realloc(tablica, liczba_wierszy*sizeof(int*)) );
            --maxr;
        }
        else
        {
            tablica[i] = static_cast<int*>( realloc(tablica[i], sizeof(int)*t_liczba_elementow[i]) );
            ++i;
        }
    }
//wypisywanie tablicy
    print(const_cast<const int**>(tablica), t_liczba_elementow, liczba_wierszy);

//zwalnianie pamiêci
    free(t_liczba_elementow);
    for(int i=liczba_wierszy-1; i>=0; --i)
        free(tablica[i]);
    free(tablica);

    return 0;
}

void remove_row(int** const ptr_arr, int* const ptr_dim, int& arr_size, const int& row_index)
{
    int **ptr_row = ptr_arr+row_index;
    int *removed_row = *ptr_row;
    int *ptr_size = ptr_dim+row_index;

    --arr_size;
    for(long long int i=row_index; i<arr_size; ++i)
    {
        *ptr_row = *(ptr_row+1);
        *ptr_size = *(ptr_size+1);
        ptr_row++;
        ptr_size++;
    }

    free(removed_row);
}

void print(const int** ptr_arr, const int* ptr_dim, const int& arr_size)
{
    int *ptr;
    for(int i=arr_size; i>0; --i)
    {
        ptr = const_cast<int*>( *ptr_arr++ );
        for(long long int j=*ptr_dim++; j>0; --j)
            cout << *ptr++ << ' ';
        cout << '\n';
    }
    cout << '\n';
}
