#include <cstdio>
#include <stdlib.h>
#include <ctime>
#include <iostream>
#include <iomanip>
#include <string>
#include <fstream>
#include <vector>
#include <unordered_set>
#include <unordered_map>
#include <algorithm>
#include <utility>
#include <cstring>
#include <thread>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/mman.h>

#define unlikely(x)    __builtin_expect(!!(x), 0)
#define likely(x)      __builtin_expect(!!(x), 1)

using namespace std;

typedef vector<vector<int32_t>> DirectedGraph;
typedef vector<vector<int32_t>> ans_t;
// problem constraints
#define MAX_LEN 7 
#define MIN_LEN 3
#define MAX_RATIO   3
#define MIN_RATIO   0.2
#define MAX_EDGES   2000000         // maximal number of edges 
#define MAX_NODES   2*MAX_EDGES     // maximal number of nodes

// priori 

//data array
char data_buf[MAX_EDGES*3*10];  // used for storing raw test data (in char)
int32_t edges[MAX_EDGES*2];     // used for storing test data, item form: (parent, child, flow)
int32_t idMap_lg[MAX_NODES];    // map from local id to global id
int32_t strTableSize[MAX_NODES];
char strTable[MAX_NODES*10];    // map from local id to glocal id in char 

// graph array

// search ancilla
#define THREAD_NUM 4    // number of threads used in the program
char blocked[THREAD_NUM][MAX_NODES];    // block list for threads 
int32_t bag3[THREAD_NUM][MAX_NODES];    // bag3 for threads

class HWCodeCraft
{
    int32_t threadId;       // thread id
	int32_t stackPtr = 0;   // stack pointer
    int32_t loopCnt = 0;    // number of circuits found
    int32_t byteCnt[5] = {0, 0, 0, 0, 0};      // answers' lengths 
    int32_t nodeStack[8];  // fixed-size stack
    DirectedGraph &dg;
    DirectedGraph &rdg;
    ans_t &ans;
    unordered_map<int32_t, vector<int32_t>> bag2;   // presearch results of second layer nodes

public:
    HWCodeCraft(int32_t _threadId, 
                DirectedGraph &_dg,
                DirectedGraph &_rdg,
                ans_t &_ans): 
                threadId(_threadId), dg(_dg), rdg(_rdg), ans(_ans){}
    void findCircuits(int32_t startId, int32_t endId, vector<int32_t> &res)
    {
		for (int i = startId; i < endId; ++i)
        {
			preSearch(i); 
            search(0, i, i, -1);    // dfs search
            bag2.clear();
        }
        // write the answer's size
        res.push_back(loopCnt);
		for (int i = 1; i < 6; ++i)
		{
			res.push_back(byteCnt[i-1]);
		}    	
    }

private:
    inline bool checkFlows(long long m1, long long m2)
    {
        return (5 * m2 >=  m1) && (m2 <= MAX_RATIO * m1);
    }
    void getMinMax(int32_t v, int32_t &min, int32_t &max)
    {
        min = INT32_MAX, max = -1;
        int32_t len = dg[v].size();
        int32_t j = 1;
        int32_t tmp;
        while (j < len)
        {
            tmp = dg[v][j];
            min = tmp < min ? tmp : min;
            max = tmp > max ? tmp : max;
            j+=2;
        }
    }
    int32_t getLowerBoundRdg(int32_t v, int32_t s)
    {
        int32_t len = rdg[v].size();
        int32_t j = 0;
        while (j < len)   
        {
            if (rdg[v][j] > s){break;}
            j+=2;
        }
        return j;
    }
    int32_t getLowerBoundDg(int32_t v, int32_t s)
    {
        int32_t len = dg[v].size();
        int32_t j = 0;
        while (j < len)   
        {
            if (dg[v][j] > s){break;}
            j+=2;
        }
        return j;
    }
    void preSearch(int32_t startId)
    {
        int32_t j, k, l, len1, len2, len3, v1, v2, m1, m2, max, min, tmp;
        bool isTrue = false;
        getMinMax(startId, min, max);
        // find the first node larger than startId
		len1 = rdg[startId].size();
        j = getLowerBoundRdg(startId, startId);
        for (; j < len1; j+=2)
        {
            v1 = rdg[startId][j];
            m1 = rdg[startId][j+1];
            isTrue = min < MAX_RATIO * m1 || max > MIN_RATIO * m1;
            if (unlikely(!isTrue)){continue;}
            // find the first node larger than startId
            len2 = rdg[v1].size();
            k = getLowerBoundRdg(v1, startId);
            for (; k < len2; k+=2)
            {
                v2 = rdg[v1][k];
                m2 = rdg[v1][k+1];
                isTrue = checkFlows(m2, m1);
                if (unlikely(!isTrue)) {continue;}      // if the flow ratio is not match
                if(bag2.find(v2) == bag2.end())         // push the second layer node
                {
                    bag2.emplace(v2, vector<int32_t>{v1, m2, m1});
                }
                else
                {
                    bag2[v2].push_back(v1);
                    bag2[v2].push_back(m2);
                    bag2[v2].push_back(m1);
                }
                // find the first node larger than startId
                len3 = rdg[v2].size();
                l = getLowerBoundRdg(v2, startId);
                while (l < len3)
                {
                    isTrue = checkFlows(rdg[v2][l+1], m2) && rdg[v2][l] != v1;
                    if (likely(isTrue))
                    {
                        bag3[threadId][rdg[v2][l]] = startId;
                    }
                    l+=2;
                }
            }
        }
    }
    void search(int depth, int32_t v, int32_t s, int32_t m)
    {
        nodeStack[stackPtr++] = v;
        blocked[threadId][v] = 1;
		int32_t i, j, k, len1, len2, v1, v2, m1, m2, m3, tmp1, tmp2, tmp3;
        bool isTrue = false;
        // find the first node larger than startId
        len1 = dg[v].size();
        i = getLowerBoundDg(v, s);
        // start DFS search
        for (; i < len1; i+=2)
        {
            v1 = dg[v][i];
            m1 = dg[v][i+1];
            isTrue = m < 0 ? false : !checkFlows(m, m1);
            isTrue = blocked[threadId][v1] || isTrue;
            // the neighbour is currently not accessible
            if (isTrue){continue;}
            nodeStack[0] = m < 0 ? m1 : nodeStack[0];
			// if the neighbour is in bag2
            auto it = bag2.find(v1);
            if(it != bag2.end())
            {
                nodeStack[stackPtr++] = v1;
                len2 = it->second.size();
                for (j = 0; j < len2; j+=3)
				{
					v2 = it->second.at(j);
                    m2 = it->second.at(j+1);
                    m3 = it->second.at(j+2);
                    isTrue = blocked[threadId][v2] || !checkFlows(m1, m2) || !checkFlows(m3, nodeStack[0]);
					if (isTrue){continue;}
                    //
					loopCnt++;
                	nodeStack[stackPtr++] = v2;
                	// push the answer
                    for (k = 0; k < depth+3; ++k)
                    {
                        tmp1 = nodeStack[k];    // get pos
                        ans[depth].emplace_back(tmp1);
                        byteCnt[depth] += strTableSize[tmp1] + 1;
                    }
					stackPtr--;   
            	}
            	stackPtr--;    
			}
            // if current depth is less than 3 or equal to 3 but able to go back to s
        	isTrue = depth < MAX_LEN - 4 || (depth == MAX_LEN-4 && bag3[threadId][v1] == s); 
        	if (isTrue)        
        	{
            	search(depth+1, v1, s, m1);
        	}	  
        }
        blocked[threadId][v] = 0;
        stackPtr--;
    }
};

// This function must only be used in this file
int32_t getNextPos(const char* buf, int32_t pos, int32_t end)
{ 
    while (buf[pos] != ',' && buf[pos] != '\n' && pos < end)
    {
        pos++;
    }
    return pos+1;
}

// this function read data in the ids array
int32_t readDataByMmap(string fileName)
{
    int32_t i, edgesIdx, len, parent, child, flow;
    // open file
    struct stat fileStat;
    int fd = open(fileName.c_str(), O_RDONLY);    
    if (fd < 0 || fstat(fd, &fileStat) != 0)
    {
        return -1;
    }
    len = fileStat.st_size;
    // create mmap 
    char *dataPtr = (char*)mmap(NULL, len, PROT_READ,
                                MAP_SHARED, fd, 0);
    if (dataPtr == MAP_FAILED)
    {
        close(fd);
        return -1;
    }
    memcpy(data_buf, dataPtr, len);
    // parse file
    i = 0;
    edgesIdx = 0;
    while (i < len)
    {
        // parent node
        parent = atoi(&data_buf[i]);
        i = getNextPos(data_buf, i, len);
        // child node
        child = atoi(&data_buf[i]);
        i = getNextPos(data_buf, i, len);
        // flow
        flow =atoi(&data_buf[i]);
        i = getNextPos(data_buf, i, len);
        if (unlikely(parent == child)){continue;}
        edges[edgesIdx] = parent;
        edges[edgesIdx+1] = child;
        edges[edgesIdx+2] = flow;
        edgesIdx += 3;
    }
    // close the mmap and file
    munmap(dataPtr, len);
    close(fd);
    return edgesIdx;   
}

/* enlarge file by using ftruncate */
bool enlargeFile_ftrc(int fileHandle, off_t newSize)
{
    // enlarge file
    if (ftruncate(fileHandle, newSize) != 0)
    {
        cout << "enlargeFile: file to invoke ftruncate." << endl;
        return false;
    }
    return true;
}

// subroutine for writeResult
void myWrite(char *ptr, 
           vector<vector<int32_t>*> &ansPtrs, 
           vector<int> &ansLen)
{
    int32_t i, j, k, len1, len2, tmp, tmp1, tmp2;
    unsigned long long byteCnt = 0; 
    vector<int32_t> *dataPtr = nullptr;
    for (i = 0; i < ansPtrs.size(); ++i)
    {
        dataPtr = ansPtrs[i];
        len1 = dataPtr->size();
        tmp = ansLen[i];
        for (j = 0; j < len1; j+=tmp)
        {
            k = 0;
            while (k < tmp)
            {
                tmp1 = dataPtr->at(j+k);
                memcpy(ptr+byteCnt, &strTable[10*tmp1], strTableSize[tmp1]);
                byteCnt += strTableSize[tmp1];
                ptr[byteCnt++] = ',';
                ++k; 
            }
            ptr[byteCnt-1] = '\n';
        }
    }
}

bool writeResult(string fileName,
                 vector<ans_t*> &ansPtrs,
                 vector<vector<int32_t>> &res)
{
    // open file
    int32_t i, j, tmp1;
    unsigned long long mapSize, byteCnt;
    char tmpBuf[16];
    // count the loop number and estimate the file size
    tmp1 = 0;
    mapSize = 0;
    for (i = 0; i < res.size(); ++i)
    {
        tmp1 += res[i][0];
        for (j = 1; j < res[i].size(); ++j)
        {
            mapSize += res[i][j];
        }
    }
    mapSize += sprintf(tmpBuf, "%d", tmp1) + 1;
    // open file
    int fd = open(fileName.c_str(), O_RDWR | O_CREAT, 0666);
    if (fd < 0)
    {
        cout << "fail to create fd." << endl;
        return false;
    }
    // enlarge file to hold the output data
    if (!enlargeFile_ftrc(fd, mapSize))
    {
        close(fd);
        cout << "fail to enlarge file." << endl;
        return false;
    }
    // create mmap
    char *dataPtr = (char*)mmap(NULL, mapSize, 
                                PROT_WRITE | PROT_READ,
                                MAP_SHARED, fd, 0);
    if (dataPtr == MAP_FAILED)
    {
        close(fd);
        cout << "fail to create mmap." << endl;
        return false;
    }
    // write data to the file
    byteCnt = sprintf(dataPtr, "%d", tmp1);
    dataPtr[byteCnt++] = '\n';
    // assign jobs for four threads
    unsigned long long cut = byteCnt, cut1, cut2, cut3;
    unsigned long long thred1 = 0.2 * mapSize, thred2 = 0.4 * mapSize, thred3 = 0.7 * mapSize;
    bool flag1 = true, flag2 = true, flag3 = true;
    vector<vector<int32_t>*> ansptrs1, ansptrs2, ansptrs3, ansptrs4;
    vector<int32_t> ansLen1, ansLen2, ansLen3, ansLen4;
    for (j = 1; j < res[0].size(); ++j)
    {
        for (i = 0; i < res.size(); ++i)
        {
            cut += res[i][j];
            if (flag1)
            {
                ansptrs1.push_back(&(ansPtrs[i]->at(j-1)));
                ansLen1.push_back(j+2);
                cut1 = cut;
                flag1 = cut < thred1; 
            }
            else if (flag2)
            {
                ansptrs2.push_back(&(ansPtrs[i]->at(j-1)));
                ansLen2.push_back(j+2);
                cut2 = cut;
                flag2 = cut < thred2; 
            }
            else if (flag3)
            {
                ansptrs3.push_back(&(ansPtrs[i]->at(j-1)));
                ansLen3.push_back(j+2);
                cut3 = cut;
                flag3 = cut < thred3;
            }
            else
            {
                ansptrs4.push_back(&(ansPtrs[i]->at(j-1)));
                ansLen4.push_back(j+2);
            }
            
        }
    }
    // 
    thread t1(myWrite, dataPtr+byteCnt, std::ref(ansptrs1), std::ref(ansLen1));
    thread t2(myWrite, dataPtr+cut1, std::ref(ansptrs2), std::ref(ansLen2));
    thread t3(myWrite, dataPtr+cut2, std::ref(ansptrs3), std::ref(ansLen3));
    thread t4(myWrite, dataPtr+cut3, std::ref(ansptrs4), std::ref(ansLen4));
    t1.join();
    t2.join();
    t3.join();
    t4.join();        
    munmap(dataPtr, mapSize);
    close(fd);
    return true;
}

// this function should only be used in this allplication
void sortNeighbr(int32_t* arr, int32_t begin, int32_t end)
{
    if (begin == end) {return;}
    int32_t i, j, key, key_aux;
    for (i = begin + 2; i < end; i+=2)
    {
        // record the tail element
        key = arr[i];
        key_aux = arr[i+1];
        if (key <= arr[begin])   // tail is less than head
        {
            // move the subarray all at once
            copy_backward(arr+begin, arr+i, arr+i+2);
            arr[begin] = key;
            arr[begin+1] = key_aux;
        }
        else
        {
            j = i - 2;
            while (arr[j] > key)
            {
                arr[j+2] = arr[j];
                arr[j+3] = arr[j+1];
                j -=2;
            }
            arr[j+2] = key;
            arr[j+3] = key_aux;    
        }
    }
}

int getIdMap(int32_t *_edges, int32_t len,
              int32_t *_idMap_lg, 
              unordered_map<int, int> &idMap_gl)
{
    int32_t parent, child, tmp1;
    int32_t i = 0, j = 0;
    for (; i < len; i+=2)
    {
        parent = _edges[i];
        child = _edges[i+1];
        if (idMap_gl.find(parent) == idMap_gl.end())
        {
            idMap_gl.emplace(parent, -1);
            _idMap_lg[j++] = parent;
        }
        if (idMap_gl.find(child) == idMap_gl.end())
        {
            idMap_gl.emplace(child, -1);
            _idMap_lg[j++] = child;
        }
    }
    // sort the global id
    sort(_idMap_lg, &_idMap_lg[j-1]+1);
    for (i = 0; i < j; ++i)
    {
        tmp1 = _idMap_lg[i];
        idMap_gl[tmp1] = i;
    }
    return j;
}

void buildDg(int32_t *_edges, int32_t len,
                int32_t *_idMap_lg,
                unordered_map<int, int> &idMap_gl, 
                DirectedGraph &dg)
{
    int32_t edgesIdx, i, j = dg.size(), k, tmp1, tmp2;
    for (i = 0; i < j; i++)
    {
        dg[i].reserve(30);
    }
    // construct dg and rdg
    edgesIdx = 0;
    int parent, child, flow;
    do {
        parent = idMap_gl[_edges[edgesIdx++]];
        child = idMap_gl[_edges[edgesIdx++]];
        flow = _edges[edgesIdx++];
        dg[parent].push_back(child);
        dg[parent].push_back(flow);
    } while (edgesIdx < len);
    // store the id string
    len = j / 2;
    for (i = 0; i < len; ++i)   
    {
        tmp1 = sprintf(&strTable[10*i], "%d", _idMap_lg[i]);
        strTableSize[i] = tmp1;
    }
    len = j;
    // sort the edges
    for (i = 0; i < len; ++i)
    {
        //sort(dg[i].begin(), dg[i].end());
        sortNeighbr(&dg[i][0], 0, dg[i].size());
    }
    // initialize the block list and bag3
    for (i = 0; i < THREAD_NUM / 2; ++i)
    {
        memset(blocked[i], 0, len);
        memset(bag3[i], -1, len);    
    }
}

void buildRdg(int32_t *_edges, int32_t len,
                int32_t *_idMap_lg,
                unordered_map<int, int> &idMap_gl, 
                DirectedGraph &rdg)
{
    int32_t edgesIdx, i, j = rdg.size(), k, tmp1, tmp2;
    for (i = 0; i < j; ++i)
    {
        rdg[i].reserve(30);
    }
    // construct dg and rdg
    edgesIdx = 0;
    int parent, child, flow;
    do {
        parent = idMap_gl[_edges[edgesIdx++]];
        child = idMap_gl[_edges[edgesIdx++]];
        flow = _edges[edgesIdx++];
        rdg[child].push_back(parent);
        rdg[child].push_back(flow);
    } while (edgesIdx < len);
    // store the id string
    len = j;
    for (i = len / 2; i < len; ++i)   
    {
        tmp1 = sprintf(&strTable[10*i], "%d", _idMap_lg[i]);
        strTableSize[i] = tmp1;
    }
    // sort the edges
    for (i = 0; i < len; ++i)
    {
        //sort(rdg[i].begin(), rdg[i].end());
        sortNeighbr(&rdg[i][0], 0, rdg[i].size());
    }
    // initialize the block list and bag3
    for (i = THREAD_NUM / 2; i < THREAD_NUM; ++i)
    {
        memset(blocked[i], 0, len);
        memset(bag3[i], -1, len);    
    }
}

bool buildGraph(int32_t *_edges, int32_t len,
                int32_t *_idMap_lg, 
                unordered_map<int, int> &idMap_gl, 
                DirectedGraph &dg,
                DirectedGraph &rdg)
{
    thread t1(buildDg, _edges, len, _idMap_lg, std::ref(idMap_gl), std::ref(dg));
    thread t2(buildRdg, _edges, len, _idMap_lg, std::ref(idMap_gl), std::ref(rdg));
    t1.join();
    t2.join();
}

int main(int argc, char *argv[])
{
    string file_name = "/data/test_data.txt";
    //string file_name = argv[1];
	string output_file = "/projects/student/result.txt";
    int32_t i, j, k, len;
    clock_t start, end;
    //--------------------------read data-----------------------------

    start = clock();
    len = readDataByMmap(file_name);
    if(len == -1)
    {
        cout << "fail to open file." << endl;
        return -1;
    }
    unordered_map<int32_t, int32_t> idMap_gl;   // map from global id to local id
    j = getIdMap(edges, len, idMap_lg, idMap_gl);
    end = clock();
    cout << "Time consumption for data reading: " << setprecision(6) << ((double)end - start)/CLOCKS_PER_SEC << "s." << endl;


    //-----------------------create directed graph-----------------------------------

    start = clock();
    DirectedGraph dg(j);  // row k for storing child, row k+1 for storing flows
    DirectedGraph rdg(j);
    buildGraph(edges, len, idMap_lg, idMap_gl, dg, rdg);
    end = clock();
    cout << "Time consumption for building graph: " << setprecision(6) << ((double)end - start)/CLOCKS_PER_SEC/2 << "s." << endl;

    //-------------------finding all elementary circuits with required lengths------------------------------------//
    
    start = clock();
    len = j;
    vector<vector<int32_t>> res(THREAD_NUM);
    ans_t ans1(6), ans2(6), ans3(6), ans4(6);
    
    HWCodeCraft solver1(0, dg, rdg, ans1);
    HWCodeCraft solver2(1, dg, rdg, ans2);
	HWCodeCraft solver3(2, dg, rdg, ans3);
	HWCodeCraft solver4(3, dg, rdg, ans4);

	thread t1(&HWCodeCraft::findCircuits, &solver1, 0, 0.13*0.42*len, std::ref(res[0]));
	thread t2(&HWCodeCraft::findCircuits, &solver2, 0.13*0.42*len, 0.13*len, std::ref(res[1]));
	thread t3(&HWCodeCraft::findCircuits, &solver3, 0.13*len, 0.13*1.92*len, std::ref(res[2]));
	thread t4(&HWCodeCraft::findCircuits, &solver4, 0.13*1.92*len, len, std::ref(res[3]));
    
	if(t1.joinable()){t1.join();}
	if(t2.joinable()){t2.join();}
	if(t3.joinable()){t3.join();}
	if(t4.joinable()){t4.join();}

    end = clock();
    cout << "Found " << res[0][0] + res[1][0] + res[2][0] + res[3][0] << " circuits." << endl;
    cout << "Time consumption for searching circuits: " << setprecision(6) << ((double)end - start)/CLOCKS_PER_SEC/4 << "s." << endl;
    //------------------print the results--------------------------------------------//
    
    // convert
    start = clock();
    vector<ans_t*> ansPtr {&ans1, &ans2, &ans3, &ans4};
    if(!writeResult(output_file, ansPtr, res))
    {
        cout << "fail to create output file." << endl;
        return -1;
    }
    end = clock();
    cout << "Time consumption for outputing: " << setprecision(6) << ((double)end - start)/CLOCKS_PER_SEC/4 << "s." << endl;
	//exit(0);
    
    return 0;
}


