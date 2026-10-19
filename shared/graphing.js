/* Shared engine for the quadratic graphing tools.
   Each tool page sets window.TOOL to "standard", "factored" or "vertex". */
(function(){
'use strict';

var TOOL = window.TOOL;

/* ================= exact fractions ================= */
function gcd(a,b){ a=Math.abs(a); b=Math.abs(b); while(b){ var t=a%b; a=b; b=t; } return a; }
function F(n,d){ if(d===undefined) d=1; if(d<0){ n=-n; d=-d; } var g=gcd(n,d)||1; return {n:n/g, d:d/g}; }
function add(x,y){ return F(x.n*y.d+y.n*x.d, x.d*y.d); }
function sub(x,y){ return F(x.n*y.d-y.n*x.d, x.d*y.d); }
function mul(x,y){ return F(x.n*y.n, x.d*y.d); }
function div(x,y){ return F(x.n*y.d, x.d*y.n); }
function neg(x){ return F(-x.n, x.d); }
function abs(x){ return F(Math.abs(x.n), x.d); }
function sq(x){ return mul(x,x); }
function num(x){ return x.n/x.d; }
function sgn(x){ return x.n>0 ? 1 : (x.n<0 ? -1 : 0); }
function isInt(x){ return x.d===1; }
function eq(x,y){ return x.n===y.n && x.d===y.d; }
function sqrtFrac(s){
  if(s.n<0) return null;
  var rn=Math.round(Math.sqrt(s.n)), rd=Math.round(Math.sqrt(s.d));
  return (rn*rn===s.n && rd*rd===s.d) ? F(rn,rd) : null;
}
function fmt(x){
  var s = x.n<0 ? '\u2212' : '', an=Math.abs(x.n);
  if(x.d===1) return s+an;
  var dd=x.d, t=0, f=0;
  while(dd%2===0){ dd/=2; t++; }
  while(dd%5===0){ dd/=5; f++; }
  if(dd===1) return s+(an/x.d).toFixed(Math.max(t,f));
  return s+an+'/'+x.d;
}
function fmtN(v){
  var s=Math.abs(v).toFixed(2).replace(/\.?0+$/,'');
  return (v<-0.004 ? '\u2212' : '')+s;
}
function par(x){ return '('+fmt(x)+')'; }
function parNeg(x){ return x.n<0 ? '('+fmt(x)+')' : fmt(x); }
function pt(x,y){ return '('+fmt(x)+', '+fmt(y)+')'; }
function ptN(x,y){ return '('+fmtN(x)+', '+fmtN(y)+')'; }
function parseDec(str){
  if(str==='' || !/^\d*\.?\d*$/.test(str) || str==='.') return null;
  var parts=str.split('.'), ip=parts[0]||'0', fp=parts[1]||'';
  return F(parseInt(ip+fp,10), Math.pow(10,fp.length));
}

/* ================= expression text ================= */
var X='<i>x</i>', Y='<i>y</i>';

function polyHTML(items, keepZero){
  var out='';
  items.forEach(function(it){
    var c=it[0], body=it[1];
    if(c.n===0 && !keepZero) return;
    var mag=abs(c);
    var text = body ? (eq(mag,F(1)) ? body : fmt(mag)+body) : fmt(mag);
    if(!out) out=(c.n<0 ? '\u2212' : '')+text;
    else out += (c.n<0 ? ' \u2212 ' : ' + ')+text;
  });
  return out || '0';
}
function coefStr(a){ return eq(abs(a),F(1)) ? (a.n<0 ? '\u2212' : '') : fmt(a); }
function facFactor(r){ return r.n===0 ? X : '('+X+(r.n>0 ? ' \u2212 ' : ' + ')+fmt(abs(r))+')'; }
function facJoin(p,q){
  var fp=facFactor(p), fq=facFactor(q);
  return (p.n===0 && q.n===0) ? fp+' \u00b7 '+fq : fp+fq;
}
function facRHS(m){ return coefStr(m.a)+facJoin(m.p,m.q); }
function kTerm(k){ return k.n===0 ? '' : (k.n>0 ? ' + ' : ' \u2212 ')+fmt(abs(k)); }
function eqHTML(m){
  if(m.form==='standard') return Y+' = '+polyHTML([[m.a,X+'\u00b2'],[m.b,X],[m.c,'']]);
  if(m.form==='factored') return Y+' = '+facRHS(m);
  var inner = m.h.n===0 ? X+'\u00b2' : '('+X+(m.h.n>0 ? ' \u2212 ' : ' + ')+fmt(abs(m.h))+')\u00b2';
  return Y+' = '+coefStr(m.a)+inner+kTerm(m.k);
}

/* ================= models ================= */
function finish(m){
  m.f=function(x){ return add(mul(m.a,sq(sub(x,m.h))),m.k); };
  m.y0=m.f(F(0));
  m.opensUp=sgn(m.a)>0;
  var s=div(neg(m.k),m.a);
  m.rootsExact=null; m.rootsNum=[];
  if(sgn(s)>=0){
    var r=sqrtFrac(s);
    if(s.n===0) m.rootsExact=[m.h];
    else if(r) m.rootsExact=[sub(m.h,r),add(m.h,r)];
    else { var rn=Math.sqrt(num(s)); m.rootsNum=[num(m.h)-rn, num(m.h)+rn]; }
  }
  if(m.rootsExact) m.rootsNum=m.rootsExact.map(num);
  m.win=computeWindow(m);
  return m;
}
function mkStandard(a,b,c){
  var h=neg(div(b,mul(F(2),a)));
  var k=sub(c,div(sq(b),mul(F(4),a)));
  return finish({form:'standard',a:a,b:b,c:c,h:h,k:k});
}
function mkFactored(a,p,q){
  var h=div(add(p,q),F(2));
  var k=mul(a,mul(sub(h,p),sub(h,q)));
  return finish({form:'factored',a:a,p:p,q:q,h:h,k:k});
}
function mkVertex(a,h,k){ return finish({form:'vertex',a:a,h:h,k:k}); }

function niceStep(raw){
  var p=Math.pow(10,Math.floor(Math.log10(raw))), f=raw/p;
  return (f<=1 ? 1 : f<=2 ? 2 : f<=5 ? 5 : 10)*p;
}
function computeWindow(m){
  var h=num(m.h), a=num(m.a), k=num(m.k), y0=num(m.y0);
  var xs=[0,h,2*h].concat(m.rootsNum);
  var d=m.a.d, pat=[];
  if(m.form==='vertex'){ xs.push(h-2*d, h+2*d); pat.push(k+a*4*d*d); }
  var xmin=Math.floor(Math.min.apply(null,xs))-2, xmax=Math.ceil(Math.max.apply(null,xs))+2;
  while(xmax-xmin<10){ xmin-=1; xmax+=1; }
  function fn(x){ return a*(x-h)*(x-h)+k; }
  var ys=[0,k,y0].concat(pat);
  ys.push(a>0 ? Math.min(fn(xmin),fn(xmax)) : Math.max(fn(xmin),fn(xmax)));
  var ymin0=Math.min.apply(null,ys), ymax0=Math.max.apply(null,ys);
  var span=Math.max(ymax0-ymin0,6), pad=Math.max(1,span*0.14);
  var ymin=Math.floor(ymin0-pad), ymax=Math.ceil(ymax0+pad);
  while(ymax-ymin<8){ ymin-=1; ymax+=1; }
  return {xmin:xmin, xmax:xmax, ymin:ymin, ymax:ymax,
          xstep:niceStep((xmax-xmin)/12), ystep:niceStep((ymax-ymin)/10)};
}

/* ================= problem generators ================= */
function ri(a,b){ return Math.floor(Math.random()*(b-a+1))+a; }
function nz(a,b){ var v=0; while(v===0) v=ri(a,b); return v; }
function pick(arr){ return arr[ri(0,arr.length-1)]; }
var lastKey='';

function genRootsProblem(level){
  var a,p,q,m,key,tries=0;
  do {
    tries++;
    if(level==='easy'){
      a=pick([1,-1]);
      do { p=nz(-6,6); q=nz(-6,6); } while(p===q || (p-q)%2!==0);
    } else if(level==='medium'){
      a=pick([1,-1,2,-2]);
      do { p=nz(-6,6); q=nz(-6,6); } while(p===q);
    } else {
      a=pick([1,-1,2,-2,3,-3]);
      p=ri(-7,7);
      if(Math.random()<0.15){ if(p===0) p=nz(-7,7); q=p; }
      else { do { q=ri(-7,7); } while(q===p || (p===0 && q===0)); }
    }
    m=mkFactored(F(a),F(p),F(q));
    key=[a,Math.min(p,q),Math.max(p,q)].join(',');
  } while((key===lastKey || Math.abs(num(m.k))>50 || Math.abs(num(m.y0))>60) && tries<200);
  lastKey=key;
  return {a:a,p:p,q:q};
}
function genStandard(level){
  var g=genRootsProblem(level);
  return mkStandard(F(g.a), F(-g.a*(g.p+g.q)), F(g.a*g.p*g.q));
}
function genFactored(level){
  var g=genRootsProblem(level);
  return mkFactored(F(g.a),F(g.p),F(g.q));
}
function genVertex(level){
  var a,h,k,m,key,tries=0;
  do {
    tries++;
    if(level==='easy'){ a=F(pick([1,-1])); h=ri(-5,5); k=ri(-5,5); }
    else if(level==='medium'){ a=F(pick([1,-1,2,-2,3,-3])); h=ri(-6,6); k=ri(-6,6); }
    else { a=pick([F(1,2),F(-1,2),F(2),F(-2),F(3),F(-3),F(1,2),F(-1,2)]); h=ri(-8,8); k=ri(-8,8); }
    m=mkVertex(a,F(h),F(k));
    key=[fmt(a),h,k].join(',');
  } while((key===lastKey || (eq(a,F(1)) && h===0 && k===0) || Math.abs(num(m.y0))>60) && tries<200);
  lastKey=key;
  return m;
}

/* ================= worked solutions ================= */
function T(h){ return {t:h}; }
function M(h){ return {m:h}; }

function evalLines(m,x){
  var out=[], A=coefStr(m.a), xs=fmt(x);
  if(m.form==='standard'){
    var terms=[];
    if(m.a.n!==0) terms.push({c:m.a,p:2});
    if(m.b.n!==0) terms.push({c:m.b,p:1});
    if(m.c.n!==0) terms.push({c:m.c,p:0});
    var xp='('+xs+')';
    out.push(Y+' = '+polyHTML(terms.map(function(t){ return [t.c, t.p===2 ? xp+'\u00b2' : (t.p===1 ? xp : '')]; })));
    out.push(Y+' = '+polyHTML(terms.map(function(t){ return [t.p===2 ? mul(t.c,sq(x)) : (t.p===1 ? mul(t.c,x) : t.c), '']; }), true));
    out.push(Y+' = '+fmt(m.f(x)));
  } else if(m.form==='factored'){
    var sb=function(r){ return r.n===0 ? '('+xs+')' : '('+xs+(r.n>0 ? ' \u2212 ' : ' + ')+fmt(abs(r))+')'; };
    var vp=sub(x,m.p), vq=sub(x,m.q);
    out.push(Y+' = '+A+sb(m.p)+sb(m.q));
    out.push(Y+' = '+A+'('+fmt(vp)+')('+fmt(vq)+')');
    out.push(Y+' = '+A+'('+fmt(mul(vp,vq))+')');
    out.push(Y+' = '+fmt(m.f(x)));
  } else {
    var inner = m.h.n===0 ? '('+xs+')' : '('+xs+(m.h.n>0 ? ' \u2212 ' : ' + ')+fmt(abs(m.h))+')';
    var d=sub(x,m.h), K=kTerm(m.k);
    out.push(Y+' = '+A+inner+'\u00b2'+K);
    out.push(Y+' = '+A+'('+fmt(d)+')\u00b2'+K);
    out.push(Y+' = '+A+'('+fmt(sq(d))+')'+K);
    out.push(Y+' = '+fmt(mul(m.a,sq(d)))+K);
    out.push(Y+' = '+fmt(m.f(x)));
  }
  var res=[];
  out.forEach(function(s){ if(!res.length || res[res.length-1]!==s) res.push(s); });
  return res;
}

function dirPiece(m){
  var where = m.form==='standard' ? 'in front of '+X+'\u00b2' : 'in front of the parentheses';
  var aText = 'Here <i>a</i> = '+fmt(m.a)+'.';
  if(eq(m.a,F(1))) aText='Here <i>a</i> = 1 (no number written means 1).';
  if(eq(m.a,F(-1))) aText='Here <i>a</i> = \u22121 (a minus sign with no number means \u22121).';
  return {
    id:'dir', title:'Direction of opening', prompt:'Does the parabola open up or down?',
    answer: m.opensUp ? 'Opens up' : 'Opens down',
    work:[
      T('Look at <i>a</i>, the number '+where+'. '+aText),
      T(m.opensUp ? '<i>a</i> is positive, so the parabola opens <b>up</b> (like a smile).' : '<i>a</i> is negative, so the parabola opens <b>down</b> (like a frown).')
    ],
    plot:[{type:'dir', text: m.opensUp ? 'Opens up \u2191' : 'Opens down \u2193'}]
  };
}

function yintPiece(m, optional){
  var w=[T('The y-intercept is where the graph crosses the y-axis. On the y-axis, <i>x</i> = 0.'),
         T('Substitute <i>x</i> = 0 into the equation:')];
  evalLines(m,F(0)).forEach(function(s){ w.push(M(s)); });
  w.push(T('The y-intercept is '+pt(F(0),m.y0)+'.'));
  if(m.form==='standard') w.push(T('Shortcut: in standard form, the y-intercept is always the constant <i>c</i>.'));
  return {
    id:'yint', title:'Y-intercept',
    prompt: optional ? 'Optional: where does it cross the y-axis?' : 'Where does the graph cross the y-axis?',
    answer: pt(F(0),m.y0), work:w,
    plot:[{type:'pt', kind:'yint', x:0, y:num(m.y0)}]
  };
}

function axisPiece(m){
  var w=[], h=m.h;
  if(m.form==='standard'){
    w.push(T('The axis of symmetry is a vertical line. Use the formula:'));
    w.push(M('<i>x</i> = \u2212<i>b</i> / (2<i>a</i>)'));
    w.push(T('Here <i>a</i> = '+fmt(m.a)+' and <i>b</i> = '+fmt(m.b)+'.'));
    w.push(M('<i>x</i> = \u2212'+par(m.b)+' / (2 \u00b7 '+parNeg(m.a)+')'));
    w.push(M('<i>x</i> = '+fmt(neg(m.b))+' / '+parNeg(mul(F(2),m.a))));
    w.push(M('<i>x</i> = '+fmt(h)));
  } else if(m.form==='factored'){
    w.push(T('A parabola is symmetric, so the axis of symmetry is the vertical line exactly halfway between the two x-intercepts.'));
    w.push(T('Average the x-intercepts: add them, then divide by 2.'));
    w.push(M('<i>x</i> = ('+fmt(m.p)+' + '+parNeg(m.q)+') / 2'));
    w.push(M('<i>x</i> = '+fmt(add(m.p,m.q))+' / 2'));
    w.push(M('<i>x</i> = '+fmt(h)));
  } else {
    w.push(T('The axis of symmetry is the vertical line that goes through the vertex, so it is <i>x</i> = <i>h</i>.'));
    w.push(M('<i>x</i> = '+fmt(h)));
  }
  return {
    id:'axis', title:'Axis of symmetry', prompt:'Which vertical line splits the parabola into mirror images?',
    answer:'<i>x</i> = '+fmt(h), work:w,
    plot:[{type:'vline', x:num(h), label:'x = '+fmt(h)}]
  };
}

function vertexPiece(m){
  var w=[], h=m.h, k=m.k;
  if(m.form==='vertex'){
    w.push(T('Vertex form is '+Y+' = <i>a</i>('+X+' \u2212 <i>h</i>)\u00b2 + <i>k</i>, and the vertex is (<i>h</i>, <i>k</i>).'));
    w.push(T('Find <i>h</i>: it is the number inside the parentheses, with the opposite sign.'));
    if(h.n>0) w.push(M('('+X+' \u2212 '+fmt(h)+')\u00b2  \u2192  <i>h</i> = '+fmt(h)));
    else if(h.n<0) w.push(M('('+X+' + '+fmt(abs(h))+')\u00b2 = ('+X+' \u2212 ('+fmt(h)+'))\u00b2  \u2192  <i>h</i> = '+fmt(h)));
    else w.push(M('nothing is added to or subtracted from '+X+'  \u2192  <i>h</i> = 0'));
    w.push(T('Find <i>k</i>: it is the number added or subtracted at the end.'));
    w.push(M(k.n===0 ? 'nothing is added at the end  \u2192  <i>k</i> = 0' : '<i>k</i> = '+fmt(k)));
    w.push(T('The vertex is '+pt(h,k)+'.'));
  } else {
    w.push(T('The vertex is on the axis of symmetry, so its <i>x</i>-coordinate is '+fmt(h)+'.'));
    w.push(T('Substitute <i>x</i> = '+fmt(h)+' into the equation to find the <i>y</i>-coordinate:'));
    evalLines(m,h).forEach(function(s){ w.push(M(s)); });
    w.push(T('The vertex is '+pt(h,k)+'.'));
  }
  return {
    id:'vertex', title:'Vertex', prompt:'What is the highest or lowest point?',
    answer:pt(h,k), work:w,
    plot:[{type:'pt', kind:'vertex', x:num(h), y:num(k)}]
  };
}

function factorEq(r){
  return r.n===0 ? X+' = 0' : X+(r.n>0 ? ' \u2212 ' : ' + ')+fmt(abs(r))+' = 0  \u2192  '+X+' = '+fmt(r);
}
function sortedRoots(rs){ return rs.slice().sort(function(u,v){ return num(u)-num(v); }); }
function rootsAnswer(rs){
  var s=sortedRoots(rs).map(function(r){ return pt(r,F(0)); });
  return s.length===1 ? s[0]+' (only one)' : s.join(' and ');
}

function xintFactored(m){
  var w=[];
  w.push(T('The x-intercepts are where <i>y</i> = 0. Set the equation equal to 0:'));
  w.push(M('0 = '+facRHS(m)));
  w.push(T('Zero product property: if things multiply to give 0, at least one of them must be 0. Set each factor equal to 0 and solve:'));
  var same=eq(m.p,m.q);
  w.push(M(factorEq(m.p)));
  if(!same) w.push(M(factorEq(m.q)));
  else w.push(T('Both factors give the same answer, so there is only one x-intercept.'));
  w.push(T(same ? 'The x-intercept is '+pt(m.p,F(0))+'. It is also the vertex.' : 'The x-intercepts are '+rootsAnswer([m.p,m.q])+'.'));
  return {
    id:'xint', title:'X-intercepts', prompt:'Where does the graph cross the x-axis?',
    answer:rootsAnswer(same ? [m.p] : [m.p,m.q]), work:w,
    plot:(same ? [m.p] : [m.p,m.q]).map(function(r){ return {type:'pt', kind:'xint', x:num(r), y:0}; })
  };
}

function xintStandard(m){
  var a=m.a,b=m.b,c=m.c, w=[], ans;
  w.push(T('The x-intercepts are where the graph crosses the x-axis, so <i>y</i> = 0. Set the equation equal to 0:'));
  w.push(M(polyHTML([[a,X+'\u00b2'],[b,X],[c,'']])+' = 0'));
  var D=sub(sq(b),mul(F(4),mul(a,c)));
  var allInt=isInt(a)&&isInt(b)&&isInt(c);
  var sd=sgn(D)>=0 ? sqrtFrac(D) : null;
  var ir=null;
  if(allInt && sd){
    var r1=div(add(neg(b),sd),mul(F(2),a)), r2=div(sub(neg(b),sd),mul(F(2),a));
    if(isInt(r1) && isInt(r2)) ir=[r1,r2];
  }
  if(ir){
    var bp=div(b,a), cp=div(c,a);
    if(!eq(a,F(1))){
      w.push(T(eq(a,F(-1))
        ? 'Divide every term by \u22121 so the '+X+'\u00b2 term is positive (this flips every sign):'
        : 'Divide every term by '+fmt(a)+' so the '+X+'\u00b2 term has no number in front:'));
      w.push(M(polyHTML([[F(1),X+'\u00b2'],[bp,X],[cp,'']])+' = 0'));
    }
    w.push(T('Find two numbers that multiply to '+fmt(cp)+' and add to '+fmt(bp)+'. Those numbers are '+fmt(neg(ir[0]))+' and '+fmt(neg(ir[1]))+'.'));
    w.push(T('Write the factors:'));
    w.push(M(facJoin(ir[0],ir[1])+' = 0'));
    w.push(T('Zero product property: if things multiply to give 0, at least one of them must be 0. Set each factor equal to 0 and solve:'));
    var same=eq(ir[0],ir[1]);
    w.push(M(factorEq(ir[0])));
    if(!same) w.push(M(factorEq(ir[1])));
    else w.push(T('Both factors give the same answer, so there is only one x-intercept.'));
    w.push(T(same ? 'The x-intercept is '+pt(ir[0],F(0))+'. It is also the vertex.' : 'The x-intercepts are '+rootsAnswer(ir)+'.'));
    ans=rootsAnswer(same ? [ir[0]] : ir);
  } else {
    w.push(T(allInt ? 'This one does not factor easily with whole numbers, so use the quadratic formula:' : 'Use the quadratic formula:'));
    w.push(M('<i>x</i> = (\u2212<i>b</i> \u00b1 \u221a(<i>b</i>\u00b2 \u2212 4<i>ac</i>)) / (2<i>a</i>)'));
    w.push(T('Here <i>a</i> = '+fmt(a)+', <i>b</i> = '+fmt(b)+', <i>c</i> = '+fmt(c)+'.'));
    w.push(M('<i>x</i> = (\u2212'+par(b)+' \u00b1 \u221a('+par(b)+'\u00b2 \u2212 4'+par(a)+par(c)+')) / (2'+par(a)+')'));
    w.push(M('<i>x</i> = ('+fmt(neg(b))+' \u00b1 \u221a'+fmt(D)+') / '+fmt(mul(F(2),a))));
    if(sgn(D)<0){
      w.push(T('The number under the square root is negative, and you can\u2019t take the square root of a negative number. So there are no x-intercepts: the parabola never touches the x-axis.'));
      ans='No x-intercepts';
    } else if(sgn(D)===0){
      w.push(T('\u221a0 = 0, so the \u00b1 does nothing and there is only one answer:'));
      w.push(M('<i>x</i> = '+fmt(neg(b))+' / '+fmt(mul(F(2),a))+' = '+fmt(m.h)));
      w.push(T('There is one x-intercept, and it is also the vertex.'));
      ans=pt(m.h,F(0))+' (only one)';
    } else if(sd){
      var q1=div(add(neg(b),sd),mul(F(2),a)), q2=div(sub(neg(b),sd),mul(F(2),a));
      w.push(T('\u221a'+fmt(D)+' = '+fmt(sd)+', so:'));
      w.push(M('<i>x</i> = ('+fmt(neg(b))+' + '+fmt(sd)+') / '+fmt(mul(F(2),a))+' = '+fmt(q1)));
      w.push(M('<i>x</i> = ('+fmt(neg(b))+' \u2212 '+fmt(sd)+') / '+fmt(mul(F(2),a))+' = '+fmt(q2)));
      ans=rootsAnswer([q1,q2]);
    } else {
      var sdn=Math.sqrt(num(D)), den=num(mul(F(2),a)), nb=num(neg(b));
      var n1=(nb+sdn)/den, n2=(nb-sdn)/den;
      w.push(T('\u221a'+fmt(D)+' is not a whole number. Use a calculator: \u221a'+fmt(D)+' \u2248 '+fmtN(sdn)+'.'));
      w.push(M('<i>x</i> \u2248 ('+fmt(neg(b))+' + '+fmtN(sdn)+') / '+fmt(mul(F(2),a))+' \u2248 '+fmtN(n1)));
      w.push(M('<i>x</i> \u2248 ('+fmt(neg(b))+' \u2212 '+fmtN(sdn)+') / '+fmt(mul(F(2),a))+' \u2248 '+fmtN(n2)));
      var lo=Math.min(n1,n2), hi=Math.max(n1,n2);
      ans='about '+ptN(lo,0)+' and '+ptN(hi,0);
    }
  }
  return {
    id:'xint', title:'X-intercepts', prompt:'Where does the graph cross the x-axis? (Solve for '+'x'+' when y = 0.)',
    answer:ans, work:w,
    plot:m.rootsNum.map(function(r){ return {type:'pt', kind:'xint', x:r, y:0}; })
  };
}

function extraPiece(m){
  var h=m.h, w=[], ans, plot;
  if(h.n!==0){
    var d=abs(h), mirror=mul(F(2),h);
    w.push(T('The axis of symmetry is <i>x</i> = '+fmt(h)+'. The y-intercept '+pt(F(0),m.y0)+' is '+fmt(d)+' unit'+(eq(d,F(1))?'':'s')+' to the '+(h.n>0 ? 'left' : 'right')+' of it.'));
    w.push(T('A parabola is symmetric, so the same height shows up the same distance on the other side of the axis.'));
    w.push(M('<i>x</i> = '+fmt(h)+(h.n>0 ? ' + ' : ' \u2212 ')+fmt(d)+' = '+fmt(mirror)));
    w.push(T('The matching point is '+pt(mirror,m.y0)+'.'));
    ans=pt(mirror,m.y0);
    plot=[{type:'pt', kind:'extra', x:num(mirror), y:num(m.y0)}];
  } else {
    var y1=m.f(F(1));
    w.push(T('The y-intercept sits right on the axis of symmetry, so it has no matching partner. Pick another x-value, like <i>x</i> = 1:'));
    evalLines(m,F(1)).forEach(function(s){ w.push(M(s)); });
    w.push(T('By symmetry, <i>x</i> = \u22121 has the same height. The points are '+pt(F(1),y1)+' and '+pt(F(-1),y1)+'.'));
    ans=pt(F(1),y1)+' and '+pt(F(-1),y1);
    plot=[{type:'pt', kind:'extra', x:1, y:num(y1)},{type:'pt', kind:'extra', x:-1, y:num(y1)}];
  }
  return {id:'extra', title:'Extra point', prompt:'What other point is easy to find?', answer:ans, work:w, plot:plot};
}

function curvePiece(m){
  var which = m.form==='vertex'
    ? 'Plot the vertex and the points you found.'
    : 'Plot the vertex, the intercepts, and the extra point.';
  return {
    id:'curve', title:'Draw the parabola', prompt:'Connect the points with a smooth curve.',
    answer:'A smooth, U-shaped curve through your points.',
    work:[
      T(which),
      T('Connect them with a smooth, rounded curve. Do not use straight line segments, and do not make a point at the bottom or top.'),
      T('The curve opens '+(m.opensUp ? 'up' : 'down')+'. Draw arrows on both ends because the parabola keeps going.'),
      T('Check that the two sides look like mirror images across the axis of symmetry.')
    ],
    plot:[{type:'curve'}]
  };
}

function transformPiece(m){
  var a=m.a, h=m.h, k=m.k, A=abs(a), parts=[], w=[];
  w.push(T('Start with the parent graph '+Y+' = '+X+'\u00b2, a parabola with its vertex at (0, 0). It is the dashed gray curve on the graph.'));
  if(a.n<0){ parts.push('flipped upside-down (reflected over the x-axis)'); w.push(T('<i>a</i> = '+fmt(a)+' is negative, so flip the parent graph upside-down (reflect it over the x-axis).')); }
  if(sgn(sub(A,F(1)))>0){ parts.push('stretched vertically by a factor of '+fmt(A)+' (narrower)'); w.push(T('|<i>a</i>| = '+fmt(A)+' is bigger than 1, so the graph is stretched vertically. It gets <b>narrower</b>.')); }
  else if(sgn(sub(A,F(1)))<0){ parts.push('compressed vertically by a factor of '+fmt(A)+' (wider)'); w.push(T('|<i>a</i>| = '+fmt(A)+' is between 0 and 1, so the graph is squished vertically. It gets <b>wider</b>.')); }
  else w.push(T('|<i>a</i>| = 1, so there is no stretch or squish. The graph has the same width as the parent.'));
  if(h.n>0){ parts.push('shifted right '+fmt(h)); w.push(T('<i>h</i> = '+fmt(h)+', so shift the graph <b>right</b> '+fmt(h)+'.')); }
  else if(h.n<0){ parts.push('shifted left '+fmt(abs(h))); w.push(T('<i>h</i> = '+fmt(h)+', so shift the graph <b>left</b> '+fmt(abs(h))+'.')); }
  else w.push(T('<i>h</i> = 0, so there is no left or right shift.'));
  if(k.n>0){ parts.push('shifted up '+fmt(k)); w.push(T('<i>k</i> = '+fmt(k)+', so shift the graph <b>up</b> '+fmt(k)+'.')); }
  else if(k.n<0){ parts.push('shifted down '+fmt(abs(k))); w.push(T('<i>k</i> = '+fmt(k)+', so shift the graph <b>down</b> '+fmt(abs(k))+'.')); }
  else w.push(T('<i>k</i> = 0, so there is no up or down shift.'));
  return {
    id:'transform', title:'Transformations', prompt:'How is this graph different from '+'y = x\u00b2'+'?',
    answer: parts.length ? 'Compared with '+Y+' = '+X+'\u00b2: '+parts.join(', ')+'.' : 'No transformations. This is the parent graph.',
    work:w, plot:[{type:'ghost'}]
  };
}

function patternPiece(m){
  var a=m.a, h=m.h, k=m.k, d=m.a.d, dF=F(d), d2=F(2*d);
  var o1=mul(a,sq(dF)), o2=mul(a,sq(d2)), w=[];
  w.push(T('Each point is found by moving over from the vertex, then up or down. How far you move vertically depends on <i>a</i>.'));
  w.push(T('Over '+d+' from the vertex, the vertical move is <i>a</i> \u00b7 '+d+'\u00b2.'));
  w.push(M('<i>a</i> \u00b7 '+d+'\u00b2 = '+fmt(a)+' \u00b7 '+(d*d)+' = '+fmt(o1)));
  w.push(T('Over '+(2*d)+' from the vertex, the vertical move is <i>a</i> \u00b7 '+(2*d)+'\u00b2.'));
  w.push(M('<i>a</i> \u00b7 '+(2*d)+'\u00b2 = '+fmt(a)+' \u00b7 '+(4*d*d)+' = '+fmt(o2)));
  w.push(T(m.opensUp ? 'Since <i>a</i> is positive, these moves go <b>up</b> from the vertex.' : 'Since <i>a</i> is negative, these moves go <b>down</b> from the vertex.'));
  var y1=add(k,o1), y2=add(k,o2);
  var p1=[pt(add(h,dF),y1), pt(sub(h,dF),y1)], p2=[pt(add(h,d2),y2), pt(sub(h,d2),y2)];
  w.push(M('over '+d+':  '+p1[0]+' and '+p1[1]));
  w.push(M('over '+(2*d)+':  '+p2[0]+' and '+p2[1]));
  w.push(T('Both sides match because a parabola is symmetric.'));
  var plot=[
    {type:'pt',kind:'extra',x:num(add(h,dF)),y:num(y1)},{type:'pt',kind:'extra',x:num(sub(h,dF)),y:num(y1)},
    {type:'pt',kind:'extra',x:num(add(h,d2)),y:num(y2)},{type:'pt',kind:'extra',x:num(sub(h,d2)),y:num(y2)}
  ];
  return {
    id:'points', title:'Points from the vertex', prompt:'Use the pattern to find more points.',
    answer:p1.join(' and ')+'; '+p2.join(' and '), work:w, plot:plot
  };
}

function buildPieces(m){
  if(m.form==='standard')
    return [dirPiece(m), yintPiece(m), axisPiece(m), vertexPiece(m), xintStandard(m), extraPiece(m), curvePiece(m)];
  if(m.form==='factored')
    return [dirPiece(m), xintFactored(m), axisPiece(m), vertexPiece(m), yintPiece(m), extraPiece(m), curvePiece(m)];
  return [dirPiece(m), vertexPiece(m), axisPiece(m), transformPiece(m), patternPiece(m), yintPiece(m,true), curvePiece(m)];
}

/* ================= tool settings ================= */
var TOOLS={
  standard:{
    title:'Graphing from standard form',
    lede:'Work from y = ax\u00b2 + bx + c to find the key features, then sketch the graph. Reveal each piece to check your work or see the steps.',
    task:'Find the direction of opening, y-intercept, axis of symmetry, vertex, and x-intercepts. Then sketch the graph.',
    notes:{
      easy:'a is 1 or \u22121, and the vertex lands on whole numbers.',
      medium:'a can also be 2 or \u22122, and the vertex can have a decimal.',
      hard:'a can be up to 3, with x-intercepts at 0 or just one x-intercept.',
      custom:'Type in a quadratic from your homework and work through it step by step.'
    },
    gen:genStandard,
    entryHint:'Leave the number in front of x\u00b2 or x blank if it is 1. If a term is missing, type 0.',
    entry:[{id:'a',sign:true,blank:1},{html:'<i>x</i>\u00b2'},{id:'b',sign:true,blank:1},{html:'<i>x</i>'},{id:'c',sign:true,blank:0}],
    fromEntry:function(v){ return mkStandard(v.a,v.b,v.c); }
  },
  factored:{
    title:'Graphing from factored form',
    lede:'Work from y = a(x \u2212 p)(x \u2212 q) to find the key features, then sketch the graph. Reveal each piece to check your work or see the steps.',
    task:'Find the direction of opening, x-intercepts, axis of symmetry, vertex, and y-intercept. Then sketch the graph.',
    notes:{
      easy:'a is 1 or \u22121, and the vertex lands on whole numbers.',
      medium:'a can also be 2 or \u22122, and the vertex can have a decimal.',
      hard:'a can be up to 3, with an x-intercept at 0 or a repeated factor.',
      custom:'Type in a factored quadratic from your homework and work through it step by step.'
    },
    gen:genFactored,
    entryHint:'Leave the number in front blank if it is 1. If a factor is just x, leave its box blank or type 0.',
    entry:[{id:'a',sign:true,blank:1},{html:'(<i>x</i>'},{id:'p',sign:true,blank:0,flip:true},{html:')(<i>x</i>'},{id:'q',sign:true,blank:0,flip:true},{html:')'}],
    fromEntry:function(v){ return mkFactored(v.a,v.p,v.q); }
  },
  vertex:{
    title:'Graphing from vertex form',
    lede:'Work from y = a(x \u2212 h)\u00b2 + k. Use the vertex and transformations of y = x\u00b2 to sketch the graph. Reveal each piece to check your work or see the steps.',
    task:'Find the direction of opening, vertex, and axis of symmetry. Describe the transformations, find extra points, and sketch the graph.',
    notes:{
      easy:'a is 1 or \u22121, with a vertex between \u22125 and 5.',
      medium:'a can be 2, 3, or their negatives.',
      hard:'a can also be a fraction like 1/2, so the graph is wider.',
      custom:'Type in a vertex-form quadratic from your homework and work through it step by step.'
    },
    gen:genVertex,
    entryHint:'Leave the number in front blank if it is 1. If nothing is added inside or at the end, leave the box blank or type 0.',
    entry:[{id:'a',sign:true,blank:1},{html:'(<i>x</i>'},{id:'h',sign:true,blank:0,flip:true},{html:')\u00b2'},{id:'k',sign:true,blank:0}],
    fromEntry:function(v){ return mkVertex(v.a,v.h,v.k); }
  }
};
var tool=TOOLS[TOOL];
var LEVELS=['easy','medium','hard','custom'];
var LEVEL_NAMES={easy:'Easy',medium:'Medium',hard:'Hard',custom:'Custom'};

/* ================= page ================= */
var state={level:'easy', model:null, pieces:[], lv:{}, csigns:{}};
function $(s){ return document.querySelector(s); }
function plain(h){ return h.replace(/<[^>]+>/g,''); }

function buildShell(){
  document.title=tool.title;
  var customRow='<span class="lead">'+Y+' =</span>';
  tool.entry.forEach(function(t){
    if(t.html){ customRow+='<span>'+t.html+'</span>'; return; }
    state.csigns[t.id]=1;
    customRow+='<button type="button" class="csign" data-id="'+t.id+'" id="s-'+t.id+'" aria-label="Sign for '+t.id+': plus. Tap to switch.">+</button>'+
      '<input id="in-'+t.id+'" data-id="'+t.id+'" inputmode="decimal" maxlength="6" autocomplete="off" placeholder="'+t.blank+'" aria-label="Number for '+t.id+'">';
  });
  $('#app').innerHTML =
    '<a class="back" href="../">\u2190 All quadratics tools</a>'+
    '<h1>'+tool.title+'</h1>'+
    '<p class="lede">'+tool.lede+'</p>'+
    '<div class="bar"><div class="levels" role="group" aria-label="Difficulty">'+
      LEVELS.map(function(l){ return '<button type="button" data-level="'+l+'" aria-pressed="false">'+LEVEL_NAMES[l]+'</button>'; }).join('')+
    '</div><button type="button" class="ghost" id="big" aria-pressed="false">Large text for projecting</button></div>'+
    '<p class="note" id="levelNote"></p>'+
    '<section class="panel custom" id="customPanel" hidden><h2>Check a homework problem</h2>'+
      '<p class="sub">'+tool.entryHint+'</p><div class="centry">'+customRow+'</div>'+
      '<button type="button" class="btn primary" id="cgo">Use this problem</button><p class="cmsg" id="cmsg" role="alert"></p></section>'+
    '<section class="sheet" aria-labelledby="probLabel"><p class="label" id="probLabel">Graph this parabola</p>'+
      '<p class="problem" id="problem"></p><p class="task" id="task"></p></section>'+
    '<div class="global" id="global" role="group" aria-label="Show or hide everything">'+
      '<button type="button" class="btn" id="hideAll">Hide all</button>'+
      '<button type="button" class="btn" id="showAns">Show all answers</button>'+
      '<button type="button" class="btn" id="showWork">Show all work</button>'+
      '<button type="button" class="btn primary" id="newp">New problem</button></div>'+
    '<p class="howto">For each piece, choose Hide, Answer, or Work. Work shows the answer and the steps. The graph fills in as you reveal pieces.</p>'+
    '<div class="layout"><div id="pieces"></div><figure class="figure"><div id="graph"></div><ul class="legend" id="legend"></ul></figure></div>';
}

function setLevelButtons(){
  document.querySelectorAll('.levels button').forEach(function(b){
    b.setAttribute('aria-pressed', String(b.dataset.level===state.level));
  });
  $('#levelNote').textContent=tool.notes[state.level];
  $('#customPanel').hidden = state.level!=='custom';
  var isC=state.level==='custom';
  $('#newp').textContent = isC ? 'Enter another problem' : 'New problem';
}

function loadModel(m){
  state.model=m;
  state.pieces=m ? buildPieces(m) : [];
  state.lv={};
  state.pieces.forEach(function(p){ state.lv[p.id]=0; });
  $('#problem').innerHTML = m ? eqHTML(m) : '<span class="sub">Enter an equation above to begin.</span>';
  $('#task').textContent = m ? tool.task : '';
  $('#global').hidden = !m;
  document.querySelector('.howto').hidden = !m;
  document.querySelector('.layout').hidden = !m;
  buildPiecesDOM();
  renderGraph();
}

function buildPiecesDOM(){
  $('#pieces').innerHTML = state.pieces.map(function(p){
    var lbls=['Hide','Answer','Work'];
    var segs=lbls.map(function(l,i){ return '<button type="button" data-p="'+p.id+'" data-lv="'+i+'" aria-pressed="false">'+l+'</button>'; }).join('');
    return '<article class="piece" id="piece-'+p.id+'"><div class="piece-top"><div><h2>'+p.title+'</h2><p class="prompt">'+p.prompt+'</p></div>'+
      '<div class="seg" role="group" aria-label="'+p.title+': what to show">'+segs+'</div></div>'+
      '<div class="reveal" id="rev-'+p.id+'" aria-live="polite"></div></article>';
  }).join('');
  state.pieces.forEach(updatePiece);
}

function updatePiece(p){
  var lv=state.lv[p.id];
  document.querySelectorAll('#piece-'+p.id+' .seg button').forEach(function(b){
    b.setAttribute('aria-pressed', String(+b.dataset.lv===lv));
  });
  var h='';
  if(lv>=1) h+='<p class="ans">'+p.answer+'</p>';
  if(lv===2) h+='<div class="work">'+p.work.map(function(s){
    return s.t!==undefined ? '<p class="wt">'+s.t+'</p>' : '<p class="wm">'+s.m+'</p>';
  }).join('')+'</div>';
  $('#rev-'+p.id).innerHTML=h;
}

function setAll(level){
  state.pieces.forEach(function(p){ state.lv[p.id]=level; updatePiece(p); });
  renderGraph();
}

/* ---------- graph ---------- */
function tickLabel(v){ return fmtN(parseFloat(v.toFixed(6))); }
function renderGraph(){
  var m=state.model;
  if(!m){ $('#graph').innerHTML=''; $('#legend').innerHTML=''; return; }
  var w=m.win, W=380, H=320, L=38, R=14, T0=14, B=28, pw=W-L-R, ph=H-T0-B;
  function PX(x){ return L+(x-w.xmin)/(w.xmax-w.xmin)*pw; }
  function PY(y){ return T0+(w.ymax-y)/(w.ymax-w.ymin)*ph; }
  var a=num(m.a), h=num(m.h), k=num(m.k);
  var items=[];
  state.pieces.forEach(function(p){ if(state.lv[p.id]>0) items=items.concat(p.plot||[]); });
  function has(t){ return items.some(function(i){ return i.type===t; }); }

  var s='<svg viewBox="0 0 '+W+' '+H+'" role="img" aria-label="'+graphLabel(items)+'" xmlns="http://www.w3.org/2000/svg">';
  s+='<defs><clipPath id="clip"><rect x="'+L+'" y="'+T0+'" width="'+pw+'" height="'+ph+'"/></clipPath></defs>';
  s+='<rect class="g-frame" x="'+L+'" y="'+T0+'" width="'+pw+'" height="'+ph+'"/>';
  var i, v;
  for(i=Math.ceil(w.xmin/w.xstep); i*w.xstep<=w.xmax+1e-9; i++){
    v=i*w.xstep;
    s+='<line class="g-grid" x1="'+PX(v).toFixed(1)+'" y1="'+T0+'" x2="'+PX(v).toFixed(1)+'" y2="'+(T0+ph)+'"/>';
    s+='<text class="g-tick" x="'+PX(v).toFixed(1)+'" y="'+(T0+ph+14)+'" text-anchor="middle">'+tickLabel(v)+'</text>';
  }
  for(i=Math.ceil(w.ymin/w.ystep); i*w.ystep<=w.ymax+1e-9; i++){
    v=i*w.ystep;
    s+='<line class="g-grid" x1="'+L+'" y1="'+PY(v).toFixed(1)+'" x2="'+(L+pw)+'" y2="'+PY(v).toFixed(1)+'"/>';
    s+='<text class="g-tick" x="'+(L-5)+'" y="'+(PY(v)+4).toFixed(1)+'" text-anchor="end">'+tickLabel(v)+'</text>';
  }
  s+='<line class="g-axis" x1="'+PX(0).toFixed(1)+'" y1="'+T0+'" x2="'+PX(0).toFixed(1)+'" y2="'+(T0+ph)+'"/>';
  s+='<line class="g-axis" x1="'+L+'" y1="'+PY(0).toFixed(1)+'" x2="'+(L+pw)+'" y2="'+PY(0).toFixed(1)+'"/>';
  s+='<text class="g-axname" x="'+(L+pw-4)+'" y="'+(PY(0)-6).toFixed(1)+'" text-anchor="end">x</text>';
  s+='<text class="g-axname" x="'+(PX(0)+7).toFixed(1)+'" y="'+(T0+12)+'">y</text>';

  function pathOf(fn){
    var d='', n=240, x, y;
    for(var j=0;j<=n;j++){
      x=w.xmin+(w.xmax-w.xmin)*j/n; y=fn(x);
      d+=(j?'L':'M')+PX(x).toFixed(1)+' '+PY(y).toFixed(1);
    }
    return d;
  }
  s+='<g clip-path="url(#clip)">';
  if(has('ghost')) s+='<path class="g-ghost" d="'+pathOf(function(x){ return x*x; })+'"/>';
  if(has('vline')){
    items.filter(function(i){ return i.type==='vline'; }).forEach(function(i){
      s+='<line class="g-sym" x1="'+PX(i.x).toFixed(1)+'" y1="'+T0+'" x2="'+PX(i.x).toFixed(1)+'" y2="'+(T0+ph)+'"/>';
    });
  }
  if(has('curve')) s+='<path class="g-curve" d="'+pathOf(function(x){ return a*(x-h)*(x-h)+k; })+'"/>';
  s+='</g>';

  var pts=items.filter(function(i){ return i.type==='pt'; });
  var order={extra:0, yint:1, xint:2, vertex:3};
  pts.sort(function(p1,p2){ return order[p1.kind]-order[p2.kind]; });
  var seen={};
  pts.forEach(function(p){
    var cx=PX(p.x), cy=PY(p.y);
    if(p.kind==='vertex') s+='<polygon class="g-vertex" points="'+cx.toFixed(1)+','+(cy-8).toFixed(1)+' '+(cx+8).toFixed(1)+','+cy.toFixed(1)+' '+cx.toFixed(1)+','+(cy+8).toFixed(1)+' '+(cx-8).toFixed(1)+','+cy.toFixed(1)+'"/>';
    else if(p.kind==='xint') s+='<circle class="g-xint" cx="'+cx.toFixed(1)+'" cy="'+cy.toFixed(1)+'" r="6"/>';
    else if(p.kind==='yint') s+='<rect class="g-yint" x="'+(cx-5.5).toFixed(1)+'" y="'+(cy-5.5).toFixed(1)+'" width="11" height="11"/>';
    else s+='<circle class="g-extra" cx="'+cx.toFixed(1)+'" cy="'+cy.toFixed(1)+'" r="4.5"/>';
  });
  /* labels, placed so they don't overlap each other or the markers */
  var placed=[];
  function boxOf(x,y,anchor,txt){
    var wd=txt.length*7.4+4, x0=anchor==='start' ? x : (anchor==='end' ? x-wd : x-wd/2);
    return {x0:x0, x1:x0+wd, y0:y-12, y1:y+4};
  }
  function hits(b,o){ return !(b.x1<o.x0 || b.x0>o.x1 || b.y1<o.y0 || b.y0>o.y1); }
  function fits(b){ return b.x0>=L+2 && b.x1<=L+pw-2 && b.y0>=T0+2 && b.y1<=T0+ph-2; }
  var dirItem=items.filter(function(i){ return i.type==='dir'; })[0];
  var vlines=items.filter(function(i){ return i.type==='vline'; });
  var dirPos=null;
  if(dirItem){
    var dc=[[L+8,T0+18,'start'],[L+pw-8,T0+18,'end'],[L+8,T0+ph-10,'start'],[L+pw-8,T0+ph-10,'end']];
    var avoid=[PX(0)].concat(vlines.map(function(i){ return PX(i.x); }));
    dirPos=dc[0];
    for(var di=0; di<dc.length; di++){
      var bb=boxOf(dc[di][0],dc[di][1],dc[di][2],dirItem.text);
      if(!avoid.some(function(ax){ return ax>bb.x0-8 && ax<bb.x1+8; })){ dirPos=dc[di]; break; }
    }
    placed.push(boxOf(dirPos[0],dirPos[1],dirPos[2],dirItem.text));
  }
  placed.push({x0:L+pw-16,x1:L+pw,y0:PY(0)-20,y1:PY(0)});
  placed.push({x0:PX(0),x1:PX(0)+16,y0:T0,y1:T0+16});
  pts.forEach(function(p){ var cx=PX(p.x), cy=PY(p.y); placed.push({x0:cx-10,x1:cx+10,y0:cy-10,y1:cy+10}); });
  var vlChosen=[];
  vlines.forEach(function(i){
    var ys2 = m.opensUp ? [T0+32, T0+ph-8] : [T0+ph-8, T0+32];
    var cands2=[[ys2[0],'start',6],[ys2[0],'end',-6],[ys2[1],'start',6],[ys2[1],'end',-6]];
    var pick2=null, fb=null;
    cands2.forEach(function(c){
      if(pick2) return;
      var bb=boxOf(PX(i.x)+c[2],c[0],c[1],i.label);
      if(!fits(bb)) return;
      if(!fb) fb=c;
      if(!placed.some(function(o){ return hits(bb,o); })) pick2=c;
    });
    pick2=pick2||fb||cands2[0];
    placed.push(boxOf(PX(i.x)+pick2[2],pick2[0],pick2[1],i.label));
    vlChosen.push({x:PX(i.x)+pick2[2], y:pick2[0], anchor:pick2[1], text:i.label.replace('-','\u2212')});
  });
  var prio={vertex:0, xint:1, yint:2, extra:3};
  var labelPts=pts.slice().sort(function(p1,p2){ return prio[p1.kind]-prio[p2.kind]; });
  var seenL={};
  labelPts.forEach(function(p){
    var key=p.x.toFixed(4)+','+p.y.toFixed(4);
    if(seenL[key]) return; seenL[key]=1;
    var cx=PX(p.x), cy=PY(p.y), txt=ptN(p.x,p.y);
    var cands = p.kind==='vertex'
      ? (m.opensUp ? [[0,26,'middle'],[11,22,'start'],[-11,22,'end'],[0,-16,'middle'],[11,-10,'start'],[-11,-10,'end']]
                   : [[0,-16,'middle'],[11,-10,'start'],[-11,-10,'end'],[0,26,'middle'],[11,22,'start'],[-11,22,'end']])
      : [[11,-10,'start'],[-11,-10,'end'],[11,22,'start'],[-11,22,'end'],[0,-18,'middle'],[0,28,'middle'],[26,4,'start'],[-26,4,'end']];
    var chosen=null, fallback=null, b, c;
    for(var ci=0; ci<cands.length; ci++){
      c=cands[ci]; b=boxOf(cx+c[0],cy+c[1],c[2],txt);
      if(!fits(b)) continue;
      if(!fallback) fallback={c:c,b:b};
      if(!placed.some(function(o){ return hits(b,o); })){ chosen={c:c,b:b}; break; }
    }
    chosen=chosen||fallback||{c:cands[0], b:boxOf(cx+cands[0][0],cy+cands[0][1],cands[0][2],txt)};
    placed.push(chosen.b);
    s+='<text class="g-lbl" x="'+(cx+chosen.c[0]).toFixed(1)+'" y="'+(cy+chosen.c[1]).toFixed(1)+'" text-anchor="'+chosen.c[2]+'">'+txt+'</text>';
  });
  vlChosen.forEach(function(v2){
    s+='<text class="g-lbl" x="'+v2.x.toFixed(1)+'" y="'+v2.y+'" text-anchor="'+v2.anchor+'">'+v2.text+'</text>';
  });
  if(dirItem) s+='<text class="g-dir" x="'+dirPos[0]+'" y="'+dirPos[1]+'" text-anchor="'+dirPos[2]+'">'+dirItem.text+'</text>';
  s+='</svg>';
  $('#graph').innerHTML=s;

  var kinds={vertex:['\u25c6','Vertex'], xint:['\u25cf','X-intercept'], yint:['\u25a0','Y-intercept'], extra:['\u25cb','Extra point']};
  var present={}; pts.forEach(function(p){ present[p.kind]=1; });
  var lg=Object.keys(kinds).filter(function(kk){ return present[kk]; }).map(function(kk){
    return '<li><span class="k '+kk+'">'+kinds[kk][0]+'</span>'+kinds[kk][1]+'</li>';
  });
  if(has('vline')) lg.push('<li><span class="k" style="color:var(--accent)">\u2506</span>Axis of symmetry</li>');
  if(has('ghost')) lg.push('<li><span class="k" style="color:var(--muted)">- -</span>Parent graph <i>y</i> = <i>x</i>\u00b2</li>');
  $('#legend').innerHTML=lg.join('');
}
function graphLabel(items){
  var bits=items.filter(function(i){ return i.type==='pt'; }).map(function(i){ return i.kind.replace('xint','x-intercept').replace('yint','y-intercept')+' at '+ptN(i.x,i.y); });
  if(items.some(function(i){ return i.type==='curve'; })) bits.push('parabola drawn');
  return 'Graph grid'+(bits.length ? ' showing: '+bits.join(', ') : ' with nothing plotted yet');
}

/* ---------- custom entry ---------- */
function readEntry(){
  var vals={};
  for(var i=0;i<tool.entry.length;i++){
    var t=tool.entry[i];
    if(!t.id) continue;
    var raw=$('#in-'+t.id).value.trim(), v;
    if(raw==='') v=F(t.blank);
    else { v=parseDec(raw); if(v===null) return {err:'Use only digits and a decimal point in the number boxes.'}; }
    v=mul(v,F(state.csigns[t.id]));
    if(t.flip) v=neg(v);
    vals[t.id]=v;
  }
  if(vals.a.n===0) return {err:'The number in front (a) can\u2019t be 0, since that wouldn\u2019t be a quadratic.'};
  return {vals:vals};
}
function useCustom(){
  var r=readEntry();
  if(r.err){ $('#cmsg').textContent=r.err; return; }
  $('#cmsg').textContent='';
  loadModel(tool.fromEntry(r.vals));
  var first=$('#piece-dir .seg button'); if(first) first.focus({preventScroll:true});
}

function newProblem(){
  setLevelButtons();
  if(state.level==='custom'){
    $('#cmsg').textContent='';
    Object.keys(state.csigns).forEach(function(id){
      state.csigns[id]=1;
      var b=$('#s-'+id); b.textContent='+'; b.setAttribute('aria-label','Sign for '+id+': plus. Tap to switch.');
      $('#in-'+id).value='';
    });
    loadModel(null);
    var f=$('#in-a'); if(f) f.focus({preventScroll:true});
    return;
  }
  loadModel(tool.gen(state.level));
}

/* ---------- events ---------- */
document.addEventListener('click', function(e){
  var t=e.target; if(!(t instanceof Element)) return;
  var lv=t.closest('.levels button');
  if(lv){ state.level=lv.dataset.level; newProblem(); return; }
  if(t.closest('#big')){
    var on=document.documentElement.classList.toggle('big');
    $('#big').setAttribute('aria-pressed', String(on)); return;
  }
  var seg=t.closest('.seg button');
  if(seg){
    var id=seg.dataset.p; state.lv[id]=+seg.dataset.lv;
    var p=state.pieces.filter(function(x){ return x.id===id; })[0];
    updatePiece(p); renderGraph(); return;
  }
  if(t.closest('#hideAll')) return setAll(0);
  if(t.closest('#showAns')) return setAll(1);
  if(t.closest('#showWork')) return setAll(2);
  if(t.closest('#newp')) return newProblem();
  var cs=t.closest('button.csign');
  if(cs){
    var cid=cs.dataset.id; state.csigns[cid]*=-1;
    var plus=state.csigns[cid]===1;
    cs.textContent=plus ? '+' : '\u2212';
    cs.setAttribute('aria-label','Sign for '+cid+': '+(plus ? 'plus' : 'minus')+'. Tap to switch.');
    return;
  }
  if(t.closest('#cgo')) return useCustom();
});
document.addEventListener('input', function(e){
  var el=e.target;
  if(el.closest && el.closest('.centry') && el.tagName==='INPUT'){
    var v=el.value.replace(/[^0-9.]/g,'');
    var i=v.indexOf('.');
    if(i>=0) v=v.slice(0,i+1)+v.slice(i+1).replace(/\./g,'');
    el.value=v;
  }
});
document.addEventListener('focusin', function(e){
  var el=e.target;
  if(el.closest && el.closest('.centry') && el.tagName==='INPUT'){ try{ el.select(); }catch(err){} }
});
document.addEventListener('keydown', function(e){
  if(e.key==='Enter' && e.target.closest && e.target.closest('.centry') && e.target.tagName==='INPUT'){
    e.preventDefault(); useCustom();
  }
});

buildShell();
newProblem();

window.QuadTools={F:F,fmt:fmt,mkStandard:mkStandard,mkFactored:mkFactored,mkVertex:mkVertex,buildPieces:buildPieces,
  evalLines:evalLines,gen:tool.gen,eqHTML:eqHTML,state:state,num:num};
})();
