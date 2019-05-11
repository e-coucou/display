//---------------------------------------------------------------------------
//  eCoucou library
//
//------
// format ...
let valFormat = (a) => { 
        let r = (a>100) ? Math.round(a) : ( (a>1)? Math.round(a*100.0)/100 : Math.round(a*1000.0)/1000);
        return String(r).replace(/(.)(?=(\d{3})+$)/g,'$1 ');
//        return r;
        }
let average = (array) => array.reduce((a, b) => { return a + b; }) / array.length;
let averageOI = (array) => array.reduce((a, b) => { return (a | a.value) + b.value; }) / array.length;

// maths Function
//
function maxVal(array,values) {
	return Math.max(Math.max.apply(Math, array[values].map(function(o) { return o.value; })),0);
}
function minVal(array) {
	return 0;
}
function inRange(source, cible, range) {
        return (source < cible + range/2 && source > cible - range/2)?1:0;
} 
//----
// Matrice functions
//  
function covalence(A) {
    return matrixDot(A,transpose(A));
}
function normalisation(A){
    let result=[],moyenne,stDev,ind=-1;
    A.forEach((a)=>{
        let val = [], carre=[];
//        a.forEach( (c)=> {
//           val.push(c);})
        moyenne=(average(a));
        a.forEach((f)=>carre.push( (f-moyenne)*(f-moyenne) ));
        stDev = (Math.sqrt(average(carre)));
//        let stDev = (Math.sqrt(average(carre)*(val.length/(val.length-1))));
        result.push([]);ind++;
        a.forEach(b=>result[ind].push((b-moyenne)/stDev));
    });
    return {moyenne:moyenne,stDev:stDev,data:result};
}
function correlation(A) {
    let result=[],ind=-1;
    A.forEach((a)=>{
        let div=a[++ind];
        result.push([]);
        a.forEach((f)=>result[ind].push(f/div));
    });
    return result;
}
function vecteurDot(A, B) {
    result = 0;
    for(i=-1;++i<A.length;) { result += A[i]*B[i];};
    return result;
}
function matrixDot(A, B) {
    var result = new Array(A.length).fill(0).map(row => new Array(B[0].length).fill(0));
    return result.map((row, i) => {
        return row.map((val, j) => {
            return A[i].reduce((sum, elm, k) => sum + (elm*B[k][j]) ,0)
        })
    })
}
function transpose(A) {
    return _.unzip(A);
}
function Givens(n,i,j,at) {
    let G = zeros(n,n);
    for (x=-1;++x<n;) {
        for (y=-1;++y<n;) {
            if (x==y) { G[x][y] = (x==i || y==j) ? Math.cos(at): 1; }
            if (x==i && y==j) G[x][y]= -Math.sin(at);
            if (x==j && y==i) G[x][y]= Math.sin(at);
        }
    }
    return G;
}
function zeros(n,m) {
    let Z=[];
    for(i=-1;++i<n;) {
        Z.push([]);
        for(j=-1;++j<m;) {
            Z[i].push(0);
        }
    }
    return Z;
}
function zerosV(n) {
    let Z=[];
    for(i=-1;++i<n;) {
        Z.push(0);
    }
    return Z;
}
//---------------------------------------
// diagonalisation matrice ...
//
function jacobi(M,n,dim,limite) {
    console.log('M initial : ',M);
    let l; let V = zeros(dim,dim);
    for (i=-1;++i<dim;) V[i][i]=1;
    for (l=-1;++l<n;) {
        let i=0, j=1, seuil=0;
        for(let x=0; x<dim; x++) {
            for(let y=0; y<dim;y++) {
                if (x != y ) {
                    seuil += M[x][y]*M[x][y];
                    if (Math.abs(M[x][y]) > Math.abs(M[i][j])) { i=x; j=y;}
                }
            }
        }// end boucle i,j
//        console.log(seuil);
        if (seuil <= limite) return M;
        // on remplace par matrice de Givens
        let a=((M[j][j]-M[i][i]) / (2.0*M[i][j]) )*1.0;
//        console.log(i,j,a);
        if (a>=0) { a= -a + Math.sqrt(a*a+1);} else { a = -a - Math.sqrt(a*a+1);}
        at=Math.atan(a);
//        console.log('atan : ',at);
        let G = Givens(dim, i, j, at);
        let Gt = transpose(G);
        V=matrixDot(V,Gt);
//        console.log('G,Gr,M : ',G,Gt,M);
//        console.log(G,Gt);
        // calcul nouvel Matrice M = GMGt
        M = matrixDot(G,M);
        M = matrixDot(M,Gt);
    } // boucle
    let Vt = transpose(V);
    let T = matrixDot(V,M);
    T = matrixDot(T,Vt);
    console.log('old M ? : ',T);
    console.log('result M ; ',M);
    console.log('vectors ? :',V);
    let val=[];
    M.forEach((a,i)=>val.push(a[i,i]));
    return {vecteurs: V, valeurs: val};
}
//--------------
// en dev ... non fonctionnel !
//---------------
// jacobi test !
function jacobiV2(M,nrot,n,limite) {
/*	Computes all eigenvalues and eigenvectors of a real symmetric matrix a[1..n][1..n]. On
	output, elements of a above the diagonal are destroyed. d[1..n] returns the eigenvalues of a.
	v[1..n][1..n] is a matrix whose columns contain, on output, the normalized eigenvectors of
	a. nrot returns the number of Jacobi rotations that were required.    console.log('M initial : ',M);
	function ROTATE(a,i,j,k,l) {
		g=a[i][j];h=a[k][l];a[i][j]=g-s*(h+g*tau);a[k][l]=h+s*(g-h*tau);
	}
*/
    var a = M.slice();
	var b=zerosV(n), z=zerosV(n);
	let v=zeros(n,n), d=zerosV(n);
	let tau,g,s,ip,iq,i,j,h,tresh;
	for (ip=0;ip<n;ip++) { //Initialize to the identity matrix.
		v[ip][ip]=1.0;
	};
//console.log(v);
	for (ip=0;ip<n;ip++) { //Initialize b and d to the diagonal of a.
		b[ip]=a[ip][ip]; 
		d[ip]=a[ip][ip];
		//z[ip]=0.0; //This vector will accumulate terms of the form tapq as in equation (11.1.14).
	}
	nrot=0;
	for (i=0;++i<=50;) {
		let sm=0.0;
		for (ip=0;ip<(n-1);ip++) { //Sum off-diagonal elements.
			for (iq=ip+1;iq<n;iq++)
				sm += Math.abs(a[ip][iq]);
		}
		if (sm == 0.0) { //The normal return, which relies on quadratic convergence to machine underflow.
			// free_vector(z,1,n);
			// free_vector(b,1,n);
			console.log('Valeurs  : ',d);
			console.log('Vecteurs : ',v);
			return;
		}
		if (i < -1)
		{	tresh=0.2*sm/(n*n); //...on the first three sweeps.
		}else { tresh=0.0; } //...thereafter.
		for (ip=0;ip<(n-1);ip++) {
			for (iq=ip+1;iq<n;iq++) {
				g=100.0*Math.abs(a[ip][iq]);
				// After four sweeps, skip the rotation if the off-diagonal element is small.
//				if (i > 4 && ((Math.abs(d[ip])+g) == Math.abs(d[ip])) && ((Math.abs(d[iq])+g) == Math.abs(d[iq])) )
if (i> 4)
				{	a[ip][iq]=0.0;
				}else{ if (Math.abs(a[ip][iq]) > tresh) {
						  h=d[iq]-d[ip];
//ep						  if ((Math.abs(h)+g) == Math.abs(h))
//ep						  { t=(a[ip][iq])/h;} //t = 1/(2θ) 
//ep						  else {
							theta=0.5*h/(a[ip][iq]); // Equation (11.1.10).
							t=1.0/(Math.abs(theta)+Math.sqrt(1.0+theta*theta));
							if (theta < 0.0) t = -t;
//ep						  }
					c=1.0/Math.sqrt(1+t*t);
					s=t*c;
					tau=s/(1.0+c);
					h=t*a[ip][iq];
					z[ip] -= h;	z[iq] += h;
					d[ip] -= h;	d[iq] += h;
					a[ip][iq]=0.0;
					for (j=0;j<(ip-1);j++) { //Case of rotations 1 ≤ j < p.
//						ROTATE(a,j,ip,j,iq)
//						ROTATE(a,i,j, k,l)
//                      g=a[i][j];h=a[k][l];a[i][j]=g-s*(h+g*tau);a[k][l]=h+s*(g-h*tau);
						g=a[j][ip];h=a[j][iq];a[j][ip]=g-s*(h+g*tau);a[j][iq]=h+s*(g-h*tau);
					}
					for (j=ip+1;j<iq-1;j++) { //Case of rotations p < j < q.
//						ROTATE(a,ip,j,j,iq)
//						ROTATE(a,i,j,k,l)
//                      g=a[i][j];h=a[k][l];a[i][j]=g-s*(h+g*tau);a[k][l]=h+s*(g-h*tau);
						g=a[ip][j];h=a[j][iq];a[ip][j]=g-s*(h+g*tau);a[j][iq]=h+s*(g-h*tau);
					}
					for (j=iq+1;j<n;j++) { //Case of rotations q < j ≤ n.
//						ROTATE(a,ip,j,iq,j)
//						ROTATE(a,i,j,k,l)
//                      g=a[i][j];h=a[k][l];a[i][j]=g-s*(h+g*tau);a[k][l]=h+s*(g-h*tau);
						g=a[ip][j];h=a[iq][j];a[ip][j]=g-s*(h+g*tau);a[iq][j]=h+s*(g-h*tau);
					}
					for (j=0;j<n;j++) {
//						ROTATE(v,j,ip,j,iq)
//						ROTATE(a,i,j,k,l)
//                      g=a[i][j];h=a[k][l];a[i][j]=g-s*(h+g*tau);a[k][l]=h+s*(g-h*tau);
						g=v[j][ip];h=v[j][iq];v[j][ip]=g-s*(h+g*tau);v[j][iq]=h+s*(g-h*tau);
					}
					nrot++; //console.log(nrot,sm);
				}}
			}
		}
		for (ip=0;ip<n;ip++) {
			b[ip] += z[ip];
			d[ip]=b[ip]; // Update d with the sum of tapq,
			z[ip]=0.0; //and reinitialize z.
		}
	}
	console.log("Too many iterations in routine jacobi");
} // end fonction
//---------------
// miscelaneous