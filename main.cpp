#include <bits/stdc++.h>
#define F first
#define S second
using namespace std;
const int N=20101010;

vector<int> g[N];

int n,m;

int vc_chosen=0;
int rem_n=0;
int rem_m=0;

int ch[N];

void ReadInput(){
  string t;
  cin>>t;
  assert(t=="p");
  cin>>t;
  assert(t=="td");
  cin>>n>>m;
  assert(n<N&&m<N);
  for (int i=0;i<m;i++){
    int a,b;
    cin>>a>>b;
    assert(a>=1&&a<=n&&a!=b&&b>=1&&b<=n);
    g[a].push_back(b);
    g[b].push_back(a);
  }
  m=0;
  for (int i=1;i<=n;i++){
    sort(g[i].begin(), g[i].end());
    g[i].erase(unique(g[i].begin(), g[i].end()), g[i].end());
    m+=(int)g[i].size();
    if (g[i].size()==0){
      rem_n++;
    }
  }
  assert(m%2==0);
  m/=2;
}

void DelEdge(int a, int b){
  for (int i = 0; i < (int)g[a].size(); i++){
    if (g[a][i] == b){
      swap(g[a][i], g[a].back());
      g[a].pop_back();
      return;
    }
  }
  assert(false);
}

void Choose(int x){
  assert(ch[x] == 0);
  ch[x] = 1;
  vc_chosen++;
  rem_n++;
  for (int nx:g[x]){
    rem_m++;
    DelEdge(nx, x);
    if (g[nx].size()==0){
      rem_n++;
    }
  }
  g[x].clear();
}

void d12Reduktio(){
  //cout<<"d12reduktio"<<endl;
  queue<int> q;
  for (int i=1;i<=n;i++){
    if (g[i].size()<=2) {
      q.push(i);
    }
  }
  while (!q.empty()){
    int x=q.front();
    q.pop();
    assert(g[x].size()<=2);
    if (g[x].size()==0) continue;

    if (g[x].size()==1){
      int r=g[x][0];
      vector<int> nbs=g[r];
      Choose(r);
      for (int nb:nbs){
        if (g[nb].size()>0&&g[nb].size()<=2){
          q.push(nb);
        }
      }
    }
    else{
      assert(g[x].size()==2);
      int a=g[x][0];
      int b=g[x][1];
      int f=0;
      for (int na:g[a]){
        if(na==b){
          f=1;
          break;
        }
      }
      if (f){
        vector<int> nba=g[a];
        vector<int> nbb=g[b];
        Choose(a);
        Choose(b);
        for (int nb:nba){
          if (g[nb].size()>0&&g[nb].size()<=2){
            q.push(nb);
          }
        }
        for (int nb:nbb){
          if (g[nb].size()>0&&g[nb].size()<=2){
            q.push(nb);
          }
        }
      }
      else{
        if (g[b].size() > g[a].size()){
          swap(a, b);
        }
        int ff=0;
        for (int nx:g[a]){
          if (nx==x) ff++;
        }
        assert(ff==1);
        for (int nx:g[b]){
          if (nx==x) ff++;
        }
        assert(ff==2);
        set<int> nba(g[a].begin(), g[a].end());
        vector<int> add;
        for (int nb:g[b]){
          assert(nb!=a);
          if (nb!=x&&nba.count(nb)==0){
            add.push_back(nb);
          }
        }
        for (int nb:g[b]){
          DelEdge(nb, b);
          rem_m++;
        }
        g[b].clear();
        DelEdge(a, x);
        rem_m++;
        g[x].clear();
        vc_chosen++;
        rem_n+=2;
        for (int y:add){
          g[a].push_back(y);
          g[y].push_back(a);
          rem_m--;
        }
        for (int nb:g[a]){
          if (g[nb].size()>0&&g[nb].size()<=2){
            q.push(nb);
          }
        }
        if (g[a].size()==0){
          rem_n++;
        }
      }
    }
  }
  //cout<<n-rem_n<<" "<<m-rem_m<<" "<<vc_chosen<<endl;
}

void assertConsistent(){
  int remn=0;
  int ml=0;
  set<pair<int, int>> es;
  for (int i=1;i<=n;i++){
    if (g[i].empty()) remn++;
    ml+=(int)g[i].size();
    for (int nx:g[i]){
      assert(es.count({i, nx})==0);
      es.insert({i, nx});
    }
  }
  for (auto e:es){
    assert(es.count({e.S, e.F})==1);
  }
  ml/=2;
  assert(remn==rem_n);
  assert(ml+rem_m==m);
}

vector<pair<int, int>> maximalMatch(){
  vector<pair<int, int>> match;
  vector<int> u(n+1);
  for (int i=1;i<=n;i++){
    for (int nx:g[i]){
      if (u[i]) break;
      if (!u[nx]){
        u[i]=1;
        u[nx]=1;
        match.push_back({i, nx});
        break;
      }
    }
  }
  return match;
}

struct BipMatching{
  vector<vector<int>> g_;
  vector<int> a_, b_;
  vector<pair<int, int> > m_;
  int n1,n2;
  vector<int> ma;
  vector<int> layer; 
  int MapTo(int x){
    int ap=lower_bound(a_.begin(), a_.end(), x)-a_.begin();
    if (ap<(int)a_.size()&&a_[ap]==x) return ap;
    int bp=lower_bound(b_.begin(), b_.end(), x)-b_.begin();
    if (bp<(int)b_.size()&&b_[bp]==x) return bp+(int)a_.size();
    assert(false);
  }
  int MapFrom(int x){
    assert(x>=0);
    if (x<(int)a_.size()){
      return a_[x];
    }
    assert(x-(int)a_.size()<(int)b_.size());
    return b_[x-(int)a_.size()];
  }
  BipMatching(const vector<int>& a, const vector<int>& b)
  : g_((int)a.size() + (int)b.size()), a_(a), b_(b), n1(a.size()), n2(b.size()), ma(a.size()+b.size()), layer(a.size()+b.size()){
  }
  void AddEdge(int a, int b){
    a=MapTo(a);
    b=MapTo(b);
    g_[a].push_back(b);
    g_[b].push_back(a);
  }
  int agdfs(int i){
    int la=layer[i];
    layer[i]=0;
    assert(la>0);
    if (i<n1){
      if (ma[i]==-1){
        assert(la==1);
        return 1;
      }else{
        assert(la>1);
        if (layer[ma[i]]==la-1){
          int ff=agdfs(ma[i]);
          if (ff) return 1;
        }
        return 0;
      }
    }else{
      for (int nx:g_[i]){
        assert(nx<n1);
        if (nx!=ma[i]&&layer[nx]==la-1){
          int ff=agdfs(nx);
          if (ff){
            ma[i]=nx;
            ma[nx]=i;
            return 1;
          }
        }
      }
      return 0;
    }
  }
  vector<pair<int, int> > Matching(){
    int iter=0;
    for (int i=0;i<n1+n2;i++){
      ma[i]=-1;
    }
    vector<int> bfs(n1+n2);
    int tofo=0;
    while (1){
      iter++;
      for (int i=0;i<n1+n2;i++){
        layer[i]=0;
      }
      int bfs1=0;
      int bfs2=0;
      for (int i=0;i<n1;i++){
        if (ma[i]==-1){
          layer[i]=1;
          bfs[bfs2++]=i;
        }
      }
      int f=0;
      while (bfs1<bfs2){
        int x=bfs[bfs1++];
        assert(layer[x]>0);
        assert(f==0);
        if (x<n1){
          for (int nx:g_[x]){
            if (nx!=ma[x]&&layer[nx]==0){
              layer[nx]=layer[x]+1;
              bfs[bfs2++]=nx;
            }
          }
        }else{
          if (ma[x]==-1){
            f=layer[x];
            break;
          }else{
            if (layer[ma[x]]==0){
              layer[ma[x]]=layer[x]+1;
              bfs[bfs2++]=ma[x];
            }
          }
        }
      }
      if (f==0) break;
      for (int i=0;i<n1;i++){
        assert(layer[i]==0||layer[i]%2==1);
      }
      for (int i=0;i<n2;i++){
        assert(layer[i+n1]==0||layer[i+n1]%2==0);
      }
      int fo=0;
      for (int i=0;i<n2;i++){
        if (layer[i+n1]==f&&ma[i+n1]==-1){
          fo+=agdfs(i+n1);
        }
      }
      assert(fo>0);
      tofo+=fo;
    }
    iter--;
    assert(iter*iter<=4*(n1+n2));
    assert(m_.size()==0);
    for (int i=0;i<n1;i++){
      if (ma[i]!=-1){
        assert(ma[i]>=n1);
        assert(ma[ma[i]]==i);
        m_.push_back({i, ma[i]});
        tofo--;
      }
    }
    for (int i=0;i<n2;i++){
      if (ma[i+n1]!=-1){
        assert(ma[ma[i+n1]]==i+n1);
      }
    }
    assert(tofo==0);
    vector<pair<int, int>> ret;
    for (auto e:m_){
      ret.push_back({MapFrom(e.F), MapFrom(e.S)});
    }
    return ret;
  }
  void dfs2(vector<int>& u, int x, vector<int>& A){
    if (u[x]) return;
    u[x]=1;
    A.push_back(MapFrom(x));
    if (x<n1){
      for (int nx:g_[x]){
        if (nx!=ma[x]){
          dfs2(u, nx, A);
        }
      }
    }else{
      assert(ma[x]!=-1);
      dfs2(u, ma[x], A);
    }
  }
  vector<int> Alternating(const vector<int>& sv) {
    vector<int> u(n1+n2);
    vector<int> A;
    for (int x:sv){
      x=MapTo(x);
      assert(x<n1);
      dfs2(u, x, A);
    }
    return A;
  }
};

int lb,ub;

void kruunuredu(){
  //cout<<"kruunureduktio"<<endl;
  auto M1=maximalMatch();
  lb=M1.size();
  ub=lb*2;
  vector<int> sta(n+1);
  for (auto e:M1){
    sta[e.F]=1;
    sta[e.S]=1;
  }
  vector<int> I,NI;
  for (int i=1;i<=n;i++){
    if ((int)g[i].size()>0&&sta[i]==0){
      I.push_back(i);
      sta[i]=2;
    }
  }
  for (int x:I){
    assert(sta[x]==2);
    for (int nx:g[x]){
      assert(sta[nx]==1||sta[nx]==3);
      if (sta[nx]==3) continue;
      NI.push_back(nx);
      sta[nx]=3;
    }
  }
  sort(I.begin(), I.end());
  sort(NI.begin(), NI.end());
  BipMatching bm(I, NI);
  for (int x:I){
    for (int nx:g[x]){
      assert(sta[x]==2&&sta[nx]==3);
      bm.AddEdge(x, nx);
    }
  }
  auto M2=bm.Matching();
  lb=max(lb, (int)M2.size());
  for (auto e:M2){
    assert(sta[e.F]==2);
    assert(sta[e.S]==3);
    sta[e.F]=4;
  }
  vector<int> I0;
  for (int x:I){
    if (sta[x]==2){
      I0.push_back(x);
    }
  }
  vector<int> A=bm.Alternating(I0);
  vector<int> H;
  for (int x:A){
    assert(sta[x]==2||sta[x]==3||sta[x]==4);
    if (sta[x]==3){
      H.push_back(x);
    }
  }
  int olb=lb;
  for (int x:H){
    Choose(x);
    lb--;
  }
  assert(olb*3>=n-rem_n);
  //cout<<n-rem_n<<" "<<m-rem_m<<" "<<vc_chosen<<endl;
}

void nemhauserredu(){
  //cout<<"nemhauser"<<endl;
  vector<int> A,B;
  for (int i=1;i<=n;i++){
    if (!g[i].empty()){
      A.push_back(i*2);
      B.push_back(i*2+1);
    }
  }
  BipMatching bm(A, B);
  for (int i=1;i<=n;i++){
    for (int nx:g[i]){
      bm.AddEdge(i*2, nx*2+1);
    }
  }
  auto M=bm.Matching();
  //cout<<"M "<<M.size()<<endl;
  vector<int> sta(n*2+2);
  for (auto e:M){
    assert(e.F%2==0&&e.S%2==1);
    sta[e.F/2]=1;
  }
  vector<int> As;
  for (int i=1;i<=n;i++){
    if (!g[i].empty() && sta[i]==0){
      As.push_back(i*2); 
    }
  }
  auto Aa=bm.Alternating(As);
  for (int i=1;i<=n;i++){
    sta[i]=0;
  }
  for (int i=1;i<=n;i++){
    if (!g[i].empty()){
      sta[i*2]=1;
    }
  }
  for (int x:Aa){
    if (x%2==1){
      sta[x]=1;
    }else{
      sta[x]=0;
    }
  }
  int vc=0;
  for (int i=2;i<=n*2+1;i++){
    if (sta[i]){
      vc++;
    }
  }
  //cout<<vc<<endl;
  assert(vc==(int)M.size());
  vector<int> H;
  for (int i=1;i<=n;i++){
    if (sta[i*2]==1&&sta[i*2+1]==1){
      H.push_back(i);
    }
  }
  lb=(int)M.size()/2;
  for (int x:H){
    lb--;
    Choose(x);
  }
  //cout<<n-rem_n<<" "<<m-rem_m<<" "<<vc_chosen<<endl;
  assert(lb*2+2>=n-rem_n);
  if (rem_n > 0){
    //cout<<rem_n<<endl;
  }
}

class Timer {
private:
  bool timing;
  std::chrono::duration<double> elapsedTime;
  std::chrono::time_point<std::chrono::steady_clock> startTime;
public:
  Timer();
  void start();
  void stop();
  std::chrono::duration<double> getTime();
};

Timer::Timer() {
  timing = false;
  elapsedTime = chrono::duration<double>(std::chrono::duration_values<double>::zero());
}

void Timer::start() {
  if (timing) return;
  timing = true;
  startTime = chrono::steady_clock::now();
}

void Timer::stop() {
  if (!timing) return;
  timing = false;
  chrono::time_point<std::chrono::steady_clock> endTime = chrono::steady_clock::now();
  elapsedTime += (endTime - startTime);
}

chrono::duration<double> Timer::getTime() {
  if (timing) {
    stop();
    chrono::duration<double> ret = elapsedTime;
    start();
    return ret;
  }
  else {
    return elapsedTime;
  }
}

int main(int argc, char** argv){
  ios_base::sync_with_stdio(0);
  cin.tie(0);
  assert(argc==2);
  string algo=string(argv[1]);
  ReadInput();
  //assertConsistent();
  cout<<n<<" "<<m<<endl;
  Timer tmr;
  tmr.start();
  if (algo=="kruunu"){
    kruunuredu();
  } else if(algo=="nt"){
    nemhauserredu();
  } else if(algo=="aste"){
    d12Reduktio();
  } else{
    assert(0);
  }
  tmr.stop();
  //assertConsistent();
  cout<<rem_n<<" "<<rem_m<<" "<<vc_chosen<<endl;
  cout<<"lb "<<lb<<endl;
  cout<<"time "<<setprecision(3)<<fixed<<tmr.getTime().count()<<endl;
}