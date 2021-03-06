var font5x7 = [{ E:[0x3e,0x49,0x49,0x49,0x41], C:[0x3e,0x41,0x41,0x41,0x22], O:[0x3e,0x41,0x41,0x41,0x3e],U:[0x3f,0x40,0x40,0x40,0x3f],
            '-':[0x0,0x8,0x8,0x8,0x0],R:[0x7E,0x9,0x19,0x29,0x46],I:[0x0,0x0,0x7F,0x0,0x0],K:[0x7F,0x8,0x14,0x22,0x40],
            Y:[0x3,0xC,0x70,0xC,0x3], ' ':[0,0,0,0,0], '/':[0x20,0x10,0x8,0x4,0x2],A:[0x7E,0x11,0x11,0x11,0x7E],B:[0x7F,0x49,0x49,0x49,0x36],
            D:[0x7F,0x41,0x41,0x42,0x3C],F:[0x7F,0x9,0x9,0x9,0x1],G:[0x3E,0x41,0x49,0x49,0x38],H:[0x7F,0x10,0x10,0x10,0x7F],
            J:[0x30,0x40,0x40,0x20,0x1F],L:[0x3F,0x40,0x40,0x40,0x40],M:[0x7F,0x2,0x4,0x2,0x7F],N:[0x7F,0x2,0xC,0x10,0x7F],
            P:[0x7F,0x9,0x9,0x9,0x6],Q:[0x3E,0x41,0x51,0x21,0x5E],S:[0x46,0x49,0x49,0x49,0x31],T:[0x1,0x1,0x7F,0x1,0x1],
            V:[0xF,0x30,0x40,0x30,0xF],W:[0x7F,0x20,0x18,0x20,0x7F],X:[0x63,0x14,0x8,0x14,0x63],Z:[0x61,0x51,0x49,0x45,0x43],
            '@':[0x0,0x38,0x44,0x28,0x0],'(':[0x0,0x0,0x3E,0x41,0x0],')':[0x0,0x41,0x3E,0x0,0x0],0:[0x1C,0x22,0x41,0x22,0x1C],
            1:[0x4,0x2,0x7F,0x0,0x0],2:[0x62,0x51,0x51,0x49,0x46],3:[0x22,0x41,0x49,0x49,0x36],
            4:[0x18,0x14,0x12,0x79,0x10],//[0x10,0x28,0x24,0x72,0x21],
            5:[0x27,0x49,0x49,0x49,0x31],6:[0x3E,0x49,0x49,0x49,0x30],7:[0x1,0x61,0x11,0xD,0x3],8:[0x36,0x49,0x49,0x49,0x36],
            9:[0x6,0x49,0x49,0x49,0x3E],o:[0x38,0x44,0x44,0x44,0x38],u:[0x3C,0x40,0x40,0x40,0x3C],c:[0x38,0x44,0x44,0x44,0x44],
            e:[0x38,0x54,0x54,0x54,0x8],a:[0x20,0x54,0x54,0x54,0x38],b:[0x3F,0x44,0x44,0x44,0x38],d:[0x38,0x44,0x44,0x44,0x3F],
            f:[0x0,0x7E,0x9,0x1,0x0],g:[0x0,0x26,0x49,0x49,0x3E],h:[0x0,0x7F,0x8,0x8,0x70],i:[0x0,0x0,0x7A,0x0,0x0],
            j:[0x0,0x20,0x40,0x3D,0x0],k:[0x0,0x7E,0x10,0x68,0x0],l:[0x0,0x2,0x3E,0x40,0x40],m:[0x7C,0x8,0x70,0x8,0x70],
            n:[0x0,0x7C,0x8,0x8,0x70],p:[0x0,0x7E,0x12,0x12,0xC],q:[0x0,0xC,0x12,0x12,0x7E],r:[0x4,0x78,0x4,0x4,0x8],
            s:[0x0,0x48,0x54,0x54,0x24],t:[0x0,0x3E,0x44,0x40,0x0],u:[0x3C,0x40,0x40,0x3C,0x40],v:[0xC,0x30,0x40,0x30,0xC],
            w:[0x1C,0x60,0x38,0x60,0x1C],x:[0x44,0x28,0x10,0x28,0x44],y:[0x26,0x48,0x48,0x3E,0x0],z:[0x64,0x54,0x54,0x4C,0x0],
            é:[0x38,0x54,0x56,0x55,0x8],è:[0x38,0x55,0x56,0x54,0x8]}]

class epAnim {

  constructor (param,message) {
    this.param = param;
    this.message=message;
    this.lettre=[];
    this.data=[];
    this.param.nbC = this.message.length;
    // nouvelle option
    this.param.espace = Math.trunc((this.param.ech-1)/4)+1;
    this.param.pixel = this.param.ech*2+this.param.espace;
    this.param.nbL = Math.trunc(this.param.width / (this.param.pixel*6)); // nb possible de caractères par Ligne
    this.param.ligne = Math.trunc(this.param.nbC/this.param.nbL+.999); // nb de ligne
    this.param.cesure = Math.round(this.param.nbC / this.param.ligne + .49); // nb de caratcères par ligne au final
    this.param.hL = (this.param.pixel*8);
    this.param.hauteur = this.param.ligne*this.param.hL;
    if (this.param.height <= this.param.hauteur) {this.param.height = this.param.hauteur +4;}
    this.set_origine(Math.trunc(this.param.width-this.param.cesure*this.param.pixel*6)/2 +this.param.pixel+this.param.x,Math.trunc((this.param.height-this.param.hauteur)/(2))+this.param.pixel+this.param.y);
    console.log(this.param)
  }
  set_origine(xo,yo) {
    this.param.xo=xo;
    this.param.yo=yo;
  }
  decode() {
    let d=[];
    for (var l in this.message) {
      this.decode_lettre(this.message[l],d,l);
    }
    return d;
  }
  decode_lettre(l,d,o) { // l= la lettre à décoder, d : la matrice ou pusher o: offset de la lettre
    let i = font5x7[0][l];
    for (var j=0;j<i.length;j++) {
      let l=[];
      for (var k=0;k<7;k++) {
        let v = i[j] & (1<<k);
        let lig = Math.trunc(o/this.param.cesure); //(o<param.cesure) ? 0 : 1;
        if (v!=0) { l.push(k+lig*this.param.hL/this.param.pixel,j+6*(o-lig*this.param.cesure),lig); d.push(l);l=[];}
      }
    }
  }
  //------------------------- on réparti les points un peu partout dans le carré [width x height]
  start() {
    this.data = this.lettre;
    for (var i=0; i<this.lettre.length;i++) {
      let x=Math.trunc(Math.random()*this.param.width) + this.param.x;
      let y=Math.trunc(Math.random()*this.param.height) + this.param.y;
      this.data[i].push(x,y);
    }
  }
  //------------------------- on initialise en décodant le message en font 5x7 et on disperse les pixels
  init() {
    this.lettre = this.decode();
    this.start();
    return this.data;
  }
  dessine(g,co) {
    if (this.param.bBG) // anime t on le BackGround
    {
      g.append('rect')
          .attr('x',this.param.x).attr('y',this.param.y)
          .attr('width',this.param.width)//-margin.left-margin.right)
          .attr('height',this.param.height)//-margin.top-margin.bottom)
          .attr('fill','black')
            .transition().duration(this.param.duree*1.3).attr('fill',this.param.cBG);
    }
    d3.selectAll('#Anim circle').remove();
    g.selectAll('circle').data(this.data).enter()
      .append('circle')
              .style('fill',d=>{return this.couleur[Math.trunc(Math.random()*5)];})
              .attr('cy',d=>{return d[4];})
              .attr('cx',d=>{return d[3];})
              .attr('r',d=> {return Math.trunc(Math.random()*5);})
            .transition().duration(this.param.duree)
              .ease(d3.easeBounce)
              .attr('transform','translate('+this.param.xo+','+this.param.yo+')')
              .attr('cy',d=>{return d[0]*this.param.pixel;})
              .attr('cx',d=>{return d[1]*this.param.pixel;})
              .attr('r',this.param.ech).style('fill',co);
  }
  
}
