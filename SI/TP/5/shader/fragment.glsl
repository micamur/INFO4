// Version d'OpenGL
#version 330

in vec2 coords;

out vec4 frag_color;

vec2 carre_complexe(vec2 v) {
    vec2 res = vec2(v[0]*v[0] - v[1]*v[1], 2*v[0]*v[1]);
    return res;
}

vec4 colormap(int n) {
    vec4 res = vec4(1.0/(2*float(n)/10.0+1),0.5,1-1.0/(float(n)+1),1.0);
    return res;
}

float module(vec2 v) {
    float res = sqrt(v[0]*v[0] + v[1]*v[1]);
    return res;
}

// Fonction appellee pour chaque fragment
void main() {
  // Affichage de la coordonnee du fragment/pixel
  // frag_color = vec4(coords,0.5,1.0);

  int n = 0;
  int N = 64;
  float S = 64;
 // vec2 z = vec2(0, 0);
  vec2 z = coords;
  for (n = 0; n < N; n++) {
    //z = carre_complexe(z) + coords;
    z = carre_complexe(z) + vec2(0.285, 0.01);
    // if (module(z) > S) {
    if (z[0] + z[1] > S) {
        break;
    }
  }
  if (n == N) {
    frag_color = vec4(1, 1, 1, 1);
  } else {
    frag_color = colormap(n);
  }

}
