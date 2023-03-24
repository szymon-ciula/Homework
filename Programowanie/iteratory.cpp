// PROGRAM ZAPEWNE NIEDOKONCZONY
#include <iostream>

using namespace std;

class List
{
    struct Node;
    struct iterator;
    Node* first;
    Node* last;
    unsigned int length;

public:
    List() : first{nullptr}, last{nullptr}, length{0} {}
    ~List()
    {
        Node* ptr=last, *buff;
        while(ptr != nullptr)
        {
            buff = ptr;
            ptr = ptr->prev;
            delete buff;
        }
    }

    inline unsigned int size() const { return length; }
    inline bool empty() const   { return (length!=0 ? false : true); }

    void add(const int val)
    {
        if(first!=nullptr)
        {
            last->next = new Node(val);
            last->next->prev = last;
            last = last->next;
        }
        else
            last = first = new Node(val);

        ++length;
    }

    void remove(const unsigned int index)
    {
        if(index<length)
        {
            Node* ptr=first;
            for(unsigned int i=0; i<index; ++i)
                ptr = ptr->next;

            if(ptr != first)
            {
                if(ptr != last)
                {
                    ptr->next->prev = ptr->prev;
                    ptr->prev->next = ptr->next;
                }
                else
                {
                    last = ptr->prev;
                    last->next = nullptr;
                }
            }
            else
            {
                if(ptr != last)
                {
                    first = ptr->next;
                    first->prev = nullptr;
                }
                else
                    last = first = nullptr;
            }

            delete ptr;
            --length;
        }
    }

    iterator begin() { return iterator(first); }
    iterator end()   { return iterator(nullptr); }

private:
    struct Node
    {
        Node* prev;
        Node* next;
        int value;

        Node(int val) : prev{nullptr}, next{nullptr}, value{val}   {}
    };

    struct iterator
    {
        Node* node;
        iterator(Node* node_) : node{node_} {}

        int& operator*()    { return node->value; }
        int& operator->()   { return node->value; }

        iterator& operator++() { node = node->next; return *this; }
        iterator operator++(int)
        {
          iterator copy = *this;
          node = node->next;
          return copy;
        }

        bool operator!=(const iterator& i) const { return node!=i.node; }
        bool operator==(const iterator& i) const { return node==i.node; }
    };
};

class Tree
{
    struct Root;
    Root* top;
    size_t length;

public:
    Tree() : top{nullptr}, length{0}    {}
    ~Tree()
    { if(top != nullptr)  delete top; }

    inline size_t size() const  { return length; }
    inline bool empty() const   { return (length>0 ? false : true); }

    void add(const int val)
    {
        Root* ptr;

        if(top != nullptr)
        {
            ptr = top;
            while(true)
            {
                if(val <= ptr->value)
                {
                    if(ptr->left != nullptr)
                        ptr = ptr->left;
                    else
                    {
                        ptr->left = new Root(val);
                        ptr->left->up = ptr;
                        break;
                    }
                }
                else
                {
                    if(ptr->right != nullptr)
                        ptr = ptr->right;
                    else
                    {
                        ptr->right = new Root(val);
                        ptr->right->up = ptr;
                        break;
                    }
                }
            }
        }
        else
            top = new Root(val);

        length++;
    }

    struct Root
    {
        int value;
        Root* up;
        Root* left;
        Root* right;

        Root(const int val) : value{val}
        {
             right = nullptr;
             left = nullptr;
             up =nullptr;
        }
        ~Root()
        {
            if(right != nullptr)    delete right;
            if(left != nullptr)     delete left;
        }
    };

    struct iterator
    {
        Root* root;
        iterator(Root* root_) : root{root_} {}

        int& operator*()    { return root->value; }
        int& operator->()   { return root->value; }

        iterator& operator++()
        {
            if(root->left != nullptr)
            {
                root = root->left;
                return *this;
            }
            else
            {

            }
        }

        /*iterator& operator++() { root = root->next; return *this; }
        iterator operator++(int)
        {
          iterator copy = *this;
          root = root->next;
          return copy;
        }*/

        bool operator!=(const iterator& i) const { return root!=i.root; }
        bool operator==(const iterator& i) const { return root==i.root; }
    };
};

int main()
{
    List lista;

    for(int i=0; i<10; ++i)
        lista.add(i);

    for(auto el : lista)
        cout << el << ' ';

    return 0;
}
