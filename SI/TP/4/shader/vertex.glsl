// Version d'OpenGL
#version 330

// Donnees d'entrée
in vec3 in_position;
in vec3 in_color;
in vec3 in_normal;

// Coefficients ambiant, diffus et spéculaire (choisis entre 0 et 1)
// uniform float pa = 0.2;
// uniform float pd = 0.4;
// uniform float ps = 0.5;

// Couleur de la composante ambiante, diffuse et spéculaire (choisies entre 0 et 1)
// uniform vec3 La = vec3(1.0, 0.0, 0.0); // rouge
// uniform vec3 Ld = vec3(0.0, 0.0, 1.0); // bleu
// uniform vec3 Ls = vec3(0.0, 1.0, 0.0); // vert
// uniform vec3 La = vec3(0.9, 0.2, 0.4); // rose
// uniform vec3 Ld = vec3(0.3, 0.4, 0.2); // vert
// uniform vec3 Ls = vec3(0.2, 0.4, 0.9); // bleu

// Couleur résultante (calculée)
// vec3 Lf;

// uniform vec3 l = vec3(0.2, 0.3, 0.6); // direction de la lumière (choisi)
// vec3 r; // réflexion de l par rapport à normal (calculé)
// vec3 e; // direction de la vision (calculé)
// uniform float s = 8;  // la brillance (choisi)

// Données de sortie
out vec4 my_color;
out vec3 vert_normal;
// vec3 vert_normal;
out vec3 e;

// Parties du calcul de la couleur résultante
vec3 ambiant;
vec3 diffus;
vec3 speculaire;

// Paramètres
uniform mat4 ModelMatrix;
uniform mat4 ViewMatrix;
uniform mat4 ProjectionMatrix;

// Point de vue de la caméra
vec4 c_4;
vec3 c;

// Fonction appellee pour chaque sommet
void main() {
  vert_normal = (transpose(inverse(ModelMatrix)) * vec4(in_normal, 0.0)).xyz;
  // Affectation de la position du sommet
  // gl_Position est défini par defaut dans GLSL
  gl_Position = ProjectionMatrix * ViewMatrix * ModelMatrix * vec4(in_position, 1.0);

  // Calcul réflexion
  // r = reflect(l, vert_normal);

  // Calcul point de vue caméra
  c_4 = inverse(ViewMatrix)*vec4(0,0,0,1);
  c = c_4.xyz;
  e = in_position - c;

  // Calcul de la couleur résultante
   // ambiant = pa*La;
    // diffus = pd*Ld*max(dot(-vert_normal, l), 0);
   // speculaire = ps*Ls*pow(max(dot(r, e), 0), s);
   // Lf = ambiant + diffus + speculaire;
   // my_color = vec4(Lf, 1.0);

  // my_color = vec4(vert_normal*0.5+0.5,1.0);
}
