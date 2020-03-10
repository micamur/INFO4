// Version d'OpenGL
#version 330

in vec4 my_color;
in vec3 e;
in vec3 vert_normal;

// Parties du calcul de la couleur résultante
vec3 ambiant;
vec3 diffus;
vec3 speculaire;

uniform float pa = 0.2;
uniform float pd = 0.4;
uniform float ps = 0.5;

 uniform vec3 La = vec3(0.9, 0.2, 0.4); // rose
 uniform vec3 Ld = vec3(0.3, 0.4, 0.2); // vert
 uniform vec3 Ls = vec3(0.2, 0.4, 0.9); // bleu

 // uniform vec3 La = vec3(1.0, 0.0, 0.0); // rouge
 // uniform vec3 Ld = vec3(0.0, 0.0, 1.0); // bleu
 // uniform vec3 Ls = vec3(0.0, 1.0, 0.0); // vert

uniform vec3 l = vec3(0.8, -0.8, -0.1); // direction de la lumière (choisie)
vec3 r; // reflexion de l par rapport à normal (calculé)

uniform float s = 8;  // la brillance (choisie)

out vec4 frag_color;

vec3 Lf;
//vec3 h;

// Fonction appellee pour chaque fragment
void main() {
     r = reflect(l, normalize(vert_normal));
     ambiant = pa*La;
     diffus = pd*Ld*max(dot(normalize(-vert_normal), l), 0);
     speculaire = ps*Ls*pow(max(dot(r, e), 0), s);
     //h = normalize(vec3(l.x + e.x, l.y + e.y, l.z + e.z));
     // h = normalize(vec3(l.x + e.x/sqrt(l.x*l.x + e.x*e.x), l.y + e.y/sqrt(l.y*l.y + e.y*e.y), l.z + e.z/sqrt(l.z*l.z + e.z*e.z)));
     // speculaire = ps*Ls*pow(max(dot(h, normalize(vert_normal)), 0), s);
     Lf = ambiant + diffus + speculaire;
     // Affectation de la couleur du fragment
      frag_color = vec4(Lf, 1.0 );
      //frag_color = vec4(mod(Lf.x, 1.0), mod(Lf.y, 1.0),mod(Lf.z, 1.0), 1.0 );

}
