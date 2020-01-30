// Version d'OpenGL
#version 130

// Donnees d'entree
in vec3 in_position;
//in vec4 in_color;

// Donnees de sortie
out vec4 out_color;

// Paramêtre (uniform)
uniform mat4 ModelMatrix; // matrice du modele
uniform mat4 ViewMatrix; // matrice de vue
uniform mat4 ProjectionMatrix; // matrice de projection


// Fonction appellee pour chaque sommet
void main()
{
  // Affectation de la position du sommet
  // "out vec4 gl_Position" est definit par defaut dans GLSL

  // Transformation MVC
  gl_Position = ProjectionMatrix * ViewMatrix * ModelMatrix * vec4(in_position, 1.0);

  //gl_Position = vec4(in_position, 1.0);

  // creation de la couleur du sommet
  out_color = vec4((in_position + vec3(1))*0.5, 1.0);

}
