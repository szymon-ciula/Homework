//Szymon Ciula
#include <iostream>
#include <iomanip>
#include <algorithm>

using namespace std;

class List;

struct Point
{
    int x, y;

    Point() = default;
    Point(const int _x, const int _y) : x{_x}, y{_y}    {}
    Point(const Point& point) : x{point.x}, y{point.y}  {}

    inline void print() const { cout << '(' << x << ", " << y << ')'; }

    inline bool operator== (const Point& point)  { return (x==point.x && y==point.y); }
    inline bool operator!= (const Point& point)  { return (x!=point.x || y!=point.y); }
    inline bool operator<  (const Point& point)  { return ( !(*this>point || *this==point) ); }
    inline bool operator>= (const Point& point)  { return !(*this<point); }
    inline bool operator<= (const Point& point)  { return !(*this>point); }
    inline bool operator>  (const Point& point)
    {   return (  x>point.x  ?  true  :  ( x<point.x ? false : (y>point.y ? true : false) )  );     }
};

struct Node
{
    Point point;
private:
    Node* prev;
    Node* next;
public:
    Node() : prev{nullptr}, next{nullptr} {}
    Node(const Point& _point) : point{Point(_point)}, prev{nullptr}, next{nullptr}  {}

    inline void print() const { point.print(); }

    friend List;
};

class List
{
    Node* first;
    Node* last;
    size_t length;
public:
    List() : first{nullptr}, last{nullptr}, length{0} {};
    ~List()
    {
        while( !empty() )
            pop_back();
    }

    inline Point& front() const { return first->point; }
    inline Point& back() const { return last->point; }
    inline size_t size() const { return length; }
    inline bool empty() const { return !(static_cast<bool>(length)); }

    Node* const push_front(const Point& point)
    {
        if(first)
        {
            first->prev = new Node(point);
            first->prev->next = first;
            first = first->prev;
        }
        else
            first = last = new Node(point);
        length++;
        return first;
    }
    Node* const push_back(const Point& point)
    {
        if(last)
        {
            last->next = new Node(point);
            last->next->prev = last;
            last = last->next;
        }
        else
            last = first = new Node(point);
        length++;
        return last;
    }
    Node* const insert(Node* node, const Point& point)
    {
        if(node)
        {
            if(node->next)
            {
                Node* ptr = new Node(point);
                ptr->prev = node;
                ptr->next = node->next;
                node->next = node->next->prev = ptr;
            }
            else
            {
                last = node->next = new Node(point);
                last->prev = node;
            }
        }
        length++;
        return node->next;
    }
    Node* const pop_front()
    {
        if( !empty() )
        {
            Node* ptr = first->next;
            if(ptr) ptr->prev = nullptr;
            else    last = nullptr;
            delete first;
            first = ptr;
        }
        length--;
        return first;
    }
    Node* const pop_back()
    {
        if( !empty() )
        {
            Node* ptr = last->prev;
            if(ptr) ptr->next = nullptr;
            else    first = nullptr;
            delete last;
            last = ptr;
        }
        length--;
        return last;
    }
    void print() const
    {
        const Node* ptr = first;
        while(ptr)
        {
            ptr->print();
            cout << '\t';
            ptr = ptr->next;
        }
        cout << endl;
    }
    void sort()
    {
        Node* ptr_last = last;
        Node* ptr;
        while(ptr_last != first)
        {
            ptr = first;
            while(ptr != ptr_last)
            {
                if(ptr->point < ptr->next->point)
                    swap(ptr->point, ptr->next->point);
                ptr = ptr->next;
            }
            ptr_last = ptr_last->prev;
        }
    }
    void merge(List& list)
    {
        if( !(empty()) )
        {
            Node* ptr = first;
            while( !(list.empty()) )
            {
                if(ptr)
                {
                    if(ptr->point >= list.front())
                        ptr = ptr->next;
                    else
                    {
                        ptr->prev = insert(ptr->prev, list.front());
                        list.pop_front();
                    }
                }
                else
                {
                    while( !(list.empty()) )
                    {
                        push_back(list.front());
                        list.pop_front();
                    }
                }
            }
        }
        else
        {
            while( !(list.empty()) )
            {
                push_back(list.front());
                list.pop_front();
            }
        }
    }
};

int main()
{
    List lista;
    Point point(5,3);
    Node* ptr = lista.push_back(Point(1,2));
    lista.insert(ptr, point);
    ptr = lista.insert(ptr, Point(5,0));

    /*lista.front().print();
    cout << '\t';
    lista.back().print();
    cout << endl;
    lista.print();*/

    lista.back().x = 11;
    lista.front().y = 23;
    //lista.print();

    lista.push_back(Point(2,3));
    lista.push_back(Point(2,5));
    lista.push_front(Point(2,2));
    lista.push_back(Point(2,2));
    lista.push_back(Point(5,3));
    lista.push_front(Point(4,2));
    lista.print();

    lista.sort();
    lista.print();
    cout << boolalpha << lista.empty() << '\t' << lista.size() << endl << endl;

    List lista2;
    lista2.push_back(Point(1,3));
    lista2.push_back(Point(2,5));
    lista2.push_front(Point(2,7));
    lista2.push_back(Point(5,8));
    lista2.push_back(Point(5,3));
    lista2.push_front(Point(4,2));
    lista2.print();
    lista2.sort();
    lista2.print();
    cout << lista2.empty() << '\t' << lista2.size() << endl << endl;

    lista.merge(lista2);
    lista.print();
    cout << lista.empty() << '\t' << lista.size() << endl;
    lista2.print();
    cout << lista2.empty() << '\t' << lista2.size() << endl << endl;

    lista.pop_back();
    lista.print();
    ptr = lista.pop_front();
    lista.print();
    lista.pop_back();
    lista.print();
    ptr = lista.pop_front();
    lista.print();
    cout << lista.empty() << '\t' << lista.size() << endl << endl;

    while( !(lista.empty()) )
    {
        lista.pop_back();
        cout << lista.empty() << '\t' << lista.size() << endl;
    }

    return 0;
}

