#include <algorithm>
#include <iostream>
#include <fstream>
#include <vector>
#include <cassert>
#include <ctime>
#include <cstdlib>
#include <climits>
#include "Graph.h"
#include "MinSpanTree.h"
#include "PrimMST.h"
#include "KruskalMST.h"
#include "DisjointSet.h"
#include "PriorityQueue.h"
#include "Data.h"


using namespace std;


PriorityQueue::PriorityQueue(const vector<int> &symbols)
{
    for (int i=0; i<symbols.size(); i++)
    {
        if (indices.count(symbols[i]) == 0)
        {
            minHeap.push_back(QueueNode(symbols[i]));
            indices[symbols[i]] = i;
        }
    }

    minHeapfy();
}

void PriorityQueue::changePriority(const QueueNode &node)
{
    // if the node does not exist, return false;
    if (indices.count(node.symbol) == 0)
    {
        return;
    }

    int index = indices[node.symbol];
    if (minHeap[index].priority < node.priority)
    {
        minHeap[index].priority = node.priority;
        downwards(index);
    }
    else if (minHeap[index].priority > node.priority)
    {
        minHeap[index].priority = node.priority;
        upwards(index);
    }
}

void PriorityQueue::pop()
{
    if (size() <= 1)
    {
        minHeap.clear();
        indices.clear();
        return;
    }

    int topSymbol = minHeap[0].symbol;

    // swap the last node to the fisrt place
    swap(0, size()-1);

    // delete the top node
    minHeap.pop_back();
    indices.erase(topSymbol);

    // downheapfy
    downwards(0);
}

bool PriorityQueue::insert(const QueueNode &node)
{
    // if the node exists, return false;
    if (indices.count(node.symbol) > 0)
    {
        return false;
    }

    minHeap.push_back(node);

    int index = size() - 1;
    indices[node.symbol] = index;
    upwards(index);

    return true;
}

void PriorityQueue::minHeapfy()
{
    // nodes which have children need downwards heapfy
    int start = (size() - 2) / 2;

    for (int i=start; i>=0; i--)
    {
        downwards(i);
    }
}

void PriorityQueue::upwards(int i)
{
    if (i <= 0)
        return;

    int parent = (i - 1) / 2;

    if (minHeap[parent].priority > minHeap[i].priority)
    {
        swap(parent, i);
        upwards(parent);
    }
}

void PriorityQueue::downwards(int i)
{
    int left = i * 2 + 1;
    int right = i * 2 + 2;

    if (right < size())
    {
        if (minHeap[i].priority <= minHeap[left].priority &&
            minHeap[i].priority <= minHeap[right].priority)
        {
            return;
        }

        int smaller =
                minHeap[left].priority<minHeap[right].priority ? left : right;

        swap(i, smaller);
        downwards(smaller);
    }
    else if (left < size())
    {
        if (minHeap[i].priority <= minHeap[left].priority)
        {
            return;
        }

        swap(i, left);
        downwards(left);
    }
}

int PrimMST::generateMST(const Graph &graph, vector<EdgeNode> &mstEdges) const
{
    vector<int> prevs(graph.getVerticeNum(), -1);
    PriorityQueue pq(graph.getVertices());
    QueueNode qNode(0, 0);
    pq.changePriority(qNode);

    int totalCost = 0;
    while (pq.size() > 0)
    {
        QueueNode top = pq.top();
        pq.pop();
        int curVertice = top.symbol;
        int curCost = top.priority;
        if (prevs[curVertice] != -1)
        {
            totalCost += curCost;
            mstEdges.push_back(
                    EdgeNode(prevs[curVertice], curVertice, curCost));
        }

        // relax edges
        vector<int> neighbors = graph.neighbors(curVertice);
        for (int i=0; i<neighbors.size(); i++)
        {
            int v = neighbors[i];
            qNode.symbol = v;
            if (pq.contain(qNode))
            {
                int cost = graph.getEdgeValue(curVertice, v);
                if (qNode.priority > cost)
                {
                    qNode.priority = cost;
                    pq.changePriority(qNode);
                    prevs[v] = curVertice; // update previous vertices
                }
            }
        }
    }

    return totalCost;
}

bool cmp(const EdgeNode &a, const EdgeNode &b)
{
    return a.value < b.value;
}

int KruskalMST::generateMST(const Graph &graph,
                            vector<EdgeNode> &mstEdges) const
{
    int verticeNum = graph.getVerticeNum();
    vector<EdgeNode> edges;
    for (int i=0; i<verticeNum-1; i++)
    {
        for (int j=i+1; j<verticeNum; j++)
        {
            if (graph.adjacent(i, j))
            {
                edges.push_back(EdgeNode(i, j, graph.getEdgeValue(i,j)));
            }
        }
    }

    sort(edges.begin(), edges.end(), cmp);
    DisjointSet sets(verticeNum);
    int n = 0;
    int totalCost = 0;
    while (mstEdges.size() != verticeNum-1 && n < edges.size())
    {
        int setX = sets.findSet(edges[n].x);
        int setY = sets.findSet(edges[n].y);
        if (setX != setY)
        {
            totalCost += edges[n].value;
            mstEdges.push_back(edges[n]);
            sets.unionSets(setX, setY);
        }

        n++;
    }

    return totalCost;
}

Graph::Graph(istream &input)
{
    input >> verticeNum;
    if (checkVerticeNum() == false)
    {
        return;
    }

    int i, j, value;
    while (input >> i >> j >> value)
    {
        addEdge(i, j, value);
    }
}

Graph::Graph(int verticeNum): verticeNum(verticeNum)
{
    checkVerticeNum();
}

Graph::Graph(int verticeNum, double density):
        edgeNum(0), verticeNum(verticeNum)
{
    if (checkVerticeNum() == false)
    {
        return;
    }

    srand(time(0));
    const int RANGE = 10;
    for (int i=0; i<verticeNum-1; i++)
    {
        for (int j=1; j<verticeNum; j++)
        {
            double prob = static_cast<double>(rand()) / RAND_MAX;

            if (prob < density)
            {
                int value = rand() % RANGE + 1;
                addEdge(i, j, value);
            }
        }
    }
}

bool Graph::adjacent(int x, int y) const
{
    assert(x>=0 && x<verticeNum && y>=0 && y<verticeNum);

    return adMatrix[x][y] > 0;
}

vector<int> Graph::neighbors(int x) const
{
    assert(x>=0 && x<verticeNum);

    vector<int> list;
    for (int i=0; i<verticeNum; i++)
    {
        if (adMatrix[x][i] > 0)
        {
            list.push_back(i);
        }
    }

    return list;
}

vector<int> Graph::getVertices() const
{
    vector<int> vertices;

    for (int i=0; i<verticeNum; i++)
    {
        vertices.push_back(i);
    }

    return vertices;
}

bool Graph::addEdge(int x, int y, int value)
{
    assert(x>=0 && x<verticeNum && y>=0 && y<verticeNum);

    if (adMatrix[x][y] > 0)
        return false;

    adMatrix[x][y] = value;
    adMatrix[y][x] = value;

    return true;
}

bool Graph::deleteEdge(int x, int y)
{
    assert(x>=0 && x<verticeNum && y>=0 && y<verticeNum);

    if (adMatrix[x][y] > 0)
    {
        adMatrix[x][y] = 0;
        adMatrix[y][x] = 0;
        return true;
    }

    return false;
}

int Graph::getEdgeValue(int x, int y) const
{
    assert(x>=0 && x<verticeNum && y>=0 && y<verticeNum);

    return adMatrix[x][y];
}

void Graph::setEdgeValue(int x, int y, int value)
{
    assert(x>=0 && x<verticeNum && y>=0 && y<verticeNum);

    adMatrix[x][y] = value;
    adMatrix[y][x] = value;
}

bool Graph::checkVerticeNum()
{
    if (verticeNum <= 0)
    {
        this->verticeNum = 0;
        return false;
    }

    adMatrix = vector<vector<int> >(verticeNum, vector<int>(verticeNum));

    return true;
}

void DisjointSet::unionSets(int x, int y)
{
    int setX = findSet(x);
    int setY = findSet(y);

    if (setX >= 0 && setY >= 0)
    {
        if (array[setX] <= array[setY])
        {
            array[setX] += array[setY];
            array[setY] = setX;
        }
        else
        {
            array[setY] += array[setX];
            array[setX] = setY;
        }
    }
}

int DisjointSet::findSet(int x)
{
    if (x < 0 || x >= array.size())
    {
        return -1;
    }

    vector<int> traces;
    while (array[x] >= 0)
    {
        traces.push_back(x);
        x = array[x];
    }

    // compress the path
    for (auto itr = traces.begin(); itr != traces.end(); ++itr)
    {
        array[*itr] = x;
    }

    return x;
}
void runMST(const Graph &graph, const MinSpanTree &mst)
{
    vector<EdgeNode> mstEdges;
    int cost = mst.generateMST(graph, mstEdges);

    cout << "Total cost of MST = " << cost << endl;
    cout << "MST's edges: " << endl;
    for (int i=0; i<mstEdges.size(); i++)
    {
        cout << "(" << mstEdges[i].x << "->" << mstEdges[i].y
             << ", cost=" << mstEdges[i].value << ") ";

        if ( (i + 1) % 5 == 0)
            cout << endl;
    }

    cout << endl;
}

int main(int argc, char *argv[])
{
    if (argc != 2)
    {
        cout << "Usage: " << argv[0] << " test_data_file" << endl;
        return 1;
    }

    ifstream input(argv[1]);
    Graph graph(input);
    input.close();

    cout << "The results of Prim Algorithm" << endl;
    runMST(graph, PrimMST());

    cout << "The results of Kruskal Algorithm" << endl;
    runMST(graph, KruskalMST());

    return 0;
}
